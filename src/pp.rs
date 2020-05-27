use std::io::{ Write, Result as IoResult };
use std::cell::RefCell;
use hashbrown::HashSet;

use crate::name::Name;
use crate::level::{ Level, InnerLevel::* };
use crate::expr::{ Expr, InnerExpr::*, Binder, BinderStyle };
use crate::tc::TypeChecker;
use crate::env::{ ArcEnv, ConstantInfo, Notation, Notation::* };
use pretty_simple::doc::{ Doc, word_wrap_val };
use pretty_simple::parenable::{ Parenable, MAX_PRIORITY };
use crate::utils::HasInstantiate;



// We're using a RefCell since we need the ability to 
// make mutable borrrows recursively, but we don't need to
// go across threads, and we always own the data.
//#[derive(Clone)]
pub struct PrettyPrinter {
    pub pp_options : PPOptions,
    pub ctx_mgr : CtxMgr,
}

impl PrettyPrinter {
    pub fn new(env : ArcEnv, options : Option<PPOptions>) -> Self {
        let pp_options = options.unwrap_or_else(|| PPOptions::new_default());
        let underscores_val = pp_options.incr_w_underscores;
        PrettyPrinter {
            pp_options,
            ctx_mgr : CtxMgr::new(env, underscores_val)
        }
    }

    pub fn pp_name(&self, n : &Name) -> Doc {
        Doc::text(format!("{}", n))
    }

    // Because all recursive calls end with `maybe_surround(n)`,
    // only the outermost item is a `Parenable` element, since
    // maybe_surround : Parenable -> Doc.
    // So you end up with Parenable { all children which get compared with self (0) < 1 }
    // meaning all children have parens, and when the level itself gets printed,
    // it usually gets called with `.maybe_surround(0)`, and !(0 < 0),
    // therefore the outermost item has no parens
    pub fn pp_level(&self, lvl : &Level) -> Parenable {
        match lvl.as_ref() {
            Max(a, b) => Doc::from("max")
                              .concat_space(self.pp_level(a).maybe_surround(1))
                              .concat_newline(self.pp_level(b).maybe_surround(1))
                              .as_parenable(0),
            IMax(a, b) => Doc::from("imax")
                               .concat_space(self.pp_level(a).maybe_surround(1))
                               .concat_newline(self.pp_level(b).maybe_surround(1))
                               .as_parenable(0),
            Param(p) => self.pp_name(p).as_parenable_max(),
            _ => {
                let (num_succs, inner) = lvl.to_offset();
                match inner.as_ref() {
                    Zero => Doc::text(format!("{}", num_succs)).as_parenable_max(),
                    _ => self.pp_level(inner)
                             .maybe_surround(1)
                             .concat("+")
                             .concat(Doc::text(format!("{}", num_succs)))
                             .as_parenable(0)
                }
            }
        }
    }

    pub fn pp_levels(&self, lvls : &Vec<Level>) -> Doc {
        let parenable_lvls = lvls.into_iter()
                                 .map(|lvl| self.pp_level(lvl).maybe_surround(0));
        word_wrap_val(parenable_lvls)
       .surround_curly()
       .group()
    }

    // `head` is usually the name of a declaration.
    // binders is a slice of ParsedBinders; you can see what that looks like
    // in the comment above the function `parse_binders`; 
    // it's essentially a telescope whose binders have been stripped and 
    // iteratively instantiated (IE so that lower binders have been instantiated
    // with the higher binders, and the body has been instantiated with 
    // all stripped binders.
    // An example would be acc.intro:
    // `acc.intro : Π (a : A), (Π (b : A), r b a → acc r b) → acc r a`
    // The second binder (b : A) needs to be instantiated with the 
    // previous item in the telescope, (a : A).
    // 
    pub fn telescope(&self, head : Option<Doc>, binders : &[ParsedBinder]) -> Vec<Doc> {
        let mut acc = Vec::with_capacity(binders.len() + 1);
        if let Some(hd) = head {
            acc.push(hd);
        }

        self.telescope_core(binders, &mut acc);
        acc
    }

    /// The example we're going to use is this hypothetical function signature :
    /// `def crazy_plus {A : Type u} [has_add A] (p q r : nat) (z : int)`
    /// What we actually get are ParsedBinder structs, but ...
    pub fn telescope_core(&self, binders : &[ParsedBinder], acc : &mut Vec<Doc>) {
        let (hd, _) = match binders.split_first() {
            Some((hd, tl)) => (hd, tl),
            None => return
        };

        // Tries to group similar items in signatures;
        // for example we would want 
        // `def add3 (a b c : nat) : nat := a + b + c`
        // to properly group (a b c : nat), instead of printing
        // def add3 (a : nat) (b : nat) (c : nat).
        // STOPS attempting to group elements if :
        // 1. It meets a typeclass instance
        // 2. It finds a point where consecutive elements have different types
        //     IE `Π (a : ℕ) (b : ℚ)`
        // 3. It finds a point where consecutive elements have different binder styles.
        //     IE `Π {a : ℕ} (b : ℕ)`
        let (group, rest) = if hd.style() == BinderStyle::InstImplicit {
            (binders.split_at(1))
        } else {
            let closure = |b : &ParsedBinder| b.style() == hd.style() && b.type_() == hd.type_();
            take_while_slice(binders, closure)
        };

        // For each element in the extracted group, if :
        // 1. The binder's name is anonymous
        // AND
        // 2. The binder does not occur explicitly in the body
        // (IE if it's an implicit argument to something in the body)
        // then render it as `_`
        // else, render it as its name.
        // FIXME : Add this as an option.
        let mapped_group = group.iter().map(|b| 
            match b.is_anon && !b.occurs_in_body {
                true => Doc::from("_"),
                false => self.pp_name(b.name())
            }
        );

        // Add `: <type>` to the extracted group of binder names in the telescope.
        // Parenthesize the type in certain cases only.
        let bare = word_wrap_val(mapped_group)
                   .concat_space(":")
                   .concat_newline(self.pp_expr(hd.type_()).maybe_surround(1).group());
        
        // Surround the whole group with the appropriate 
        // bracket style based on what kind of binders are in the group.
        let bracket_style = match hd.style() {
            BinderStyle::Default         => Doc::from("(").concat(bare).concat(")"),
            BinderStyle::Implicit        => Doc::from("{").concat(bare).concat("}"),
            BinderStyle::StrictImplicit  => Doc::from("{{").concat(bare).concat("}}"),
            BinderStyle::InstImplicit    => Doc::from("[").concat(bare).concat("]"),
        };

        // Push the group to the accumulator of `Doc` elements,
        // then execute `telescope_core` on the remaining items in the telescope
        // (The ones that could not be grouped, either because they were
        // of a different type, or different binder style)
        acc.push(bracket_style.group().nest(self.pp_options.indent));
        self.telescope_core(rest, acc)
    }

    // Used to pretty print binders generically. Sometimes gets called
    // with a telescope, sometimes gets called with bare type-level stuff (I think)
    pub fn pp_binders(&self, binders : &[ParsedBinder], inner : Parenable) -> Parenable {
        if let Some((hd, tl)) = binders.split_first() {
            if hd.is_imp() {
                self.pp_expr(hd.type_()).maybe_surround(25)
                .group()
                .nest(self.pp_options.indent)
                .concat_space("→")
                .concat(Doc::line())
                .group()
                .concat(self.pp_binders(tl, inner).maybe_surround(24))
                .as_parenable(24)
                    
            } else if hd.is_forall() {
                let (group, rest) = take_while_slice(binders, |x| x.is_forall());
                let telescoped = word_wrap_val(self.telescope(None, group).into_iter());
                Doc::from("Π")
                    .concat_space(telescoped)
                    .concat(",")
                    .concat_newline(self.pp_binders(rest, inner).maybe_surround(0))
                    .group()
                    .nest(self.pp_options.indent)
                    .as_parenable(0)
            } else {
                assert!(hd.is_lambda());
                let (group, rest) = take_while_slice(binders, |x| x.is_lambda());
                let telescoped = word_wrap_val(self.telescope(None, group).into_iter());
                Doc::from("λ")
                    .concat_space(telescoped)
                    .concat(",")
                    .concat_newline(self.pp_binders(rest, inner).maybe_surround(0))
                    .group()
                    .nest(self.pp_options.indent)
                    .as_parenable(0)

            }
        } else {
            inner
        }
    }

    // If the flag to print implicit items is set to `true`,
    // tag the names of constants with "@"; the actual printing of their
    // implicit items is done elsewhere.
    pub fn const_name(&self, n : &Name) -> Parenable {
        if !self.pp_options.implicit {
            self.pp_name(n).as_parenable_max()
        } else {
            Doc::from("@").concat(self.pp_name(n)).as_parenable_max()
        }
    }

    pub fn pp_app_core(&self, _e : &Expr) -> Parenable {
        let mut apps = Vec::new();
        let mut cursor = _e;

        while let App { fun, arg, .. } = cursor.as_ref() {
            if !self.pp_options.implicit && self.ctx_mgr.is_implicit(fun) {
                cursor = fun;
            } else {
                apps.push(arg.clone());
                cursor = fun;
            }
        }

        match cursor.as_ref() {
            _ if apps.is_empty() => self.pp_expr(cursor),
            Const { name, .. } if self.pp_options.notation => {
                match self.ctx_mgr.lookup_notation(name) {
                    Some(Prefix { priority, oper, .. }) if apps.len() == 1 => {
                        let z = &apps[apps.len() - 1];
                        Doc::from(oper)
                            .concat(Doc::newline_zero())
                            .group()
                            .concat(self.pp_expr(z).maybe_surround(priority))
                            .as_parenable(priority - 1)
                    },
                    Some(Postfix { priority, oper, .. }) if apps.len() == 1 => {
                        let z = &apps[apps.len() - 1];
                        Doc::from(self.pp_expr(z).maybe_surround(priority))
                            .concat(Doc::newline_zero())
                            .concat(oper)
                            .group()
                            .as_parenable(priority - 1)
                    },
                    Some(Infix { priority, oper, .. }) if apps.len() == 2 => {
                        let z = &apps[apps.len() - 1];
                        let s = &apps[apps.len() - 2];
                        self.pp_expr(z)
                            .maybe_surround(priority)
                            .concat(oper)
                            .concat(Doc::newline_zero())
                            .concat(self.pp_expr(s).maybe_surround(priority))
                            .as_parenable(priority - 1)
                    },
                    _ => self.print_default(cursor, &apps)
                }

            },
            _ => self.print_default(cursor, &apps)

        }
    }

    pub fn print_default(&self, _e : &Expr, apps : &Vec<Expr>) -> Parenable {
        let mut _v = Vec::with_capacity(apps.len() + 1);
        _v.push(self.pp_expr(_e).maybe_surround(MAX_PRIORITY - 1).group());
        for elem in apps.into_iter().rev() {
            _v.push(self.pp_expr(elem).maybe_surround(MAX_PRIORITY).group())
        }
        //let iter = Some(self.pp_expr(_e).maybe_surround(MAX_PRIORITY - 1).group())
        //           .into_iter()
        //           .chain(apps.into_iter().rev().map(|app| {
        //               self.pp_expr(&app).maybe_surround(MAX_PRIORITY).group()
        //           }));
        word_wrap_val(_v.into_iter())
        .group()
        .nest(self.pp_options.indent)
        .as_parenable(MAX_PRIORITY - 1)
    }

    pub fn pp_sort_core(&self, level : &Level) -> Parenable {
        if level.is_zero() && self.pp_options.notation {
            Doc::from("Prop").as_parenable_max()
        } else if let Succ(x) = level.as_ref() {
            Doc::from("Type")
            .concat_space(self.pp_level(x).maybe_surround(MAX_PRIORITY))
            .as_parenable_max()
        } else {
            Doc::from("Sort")
            .concat_space(self.pp_level(level).maybe_surround(MAX_PRIORITY))
            .as_parenable_max()
        }
    }


    pub fn pp_const_core(&self, name : &Name, levels : &Vec<Level>) -> Parenable {
        if self.ctx_mgr.tc.borrow().env.read().constant_infos.get(name).is_some() {
            self.const_name(name)
        } else {
            let uparams = if levels.is_empty() {
                Doc::from("")
                .concat(self.pp_levels(levels.as_ref()))
            } else {
                Doc::from(".")
                .concat(self.pp_levels(levels.as_ref()))
            };
            let doc = Doc::from("@")
                      .concat(self.pp_name(name))
                      .concat(uparams);

            Parenable::new_max(doc)
        }
    }

    pub fn pp_let_core(&self, binder : &Binder, val : &Expr, body : &Expr) -> Parenable {
        let suggestion = binder.clone().as_local();
        let binding = Binder::from(&suggestion);
        let fresh_lc_name = self.ctx_mgr.fresh_name(&binding.pp_name);
        let swapped_lc = suggestion.swap_local_binding_name(&fresh_lc_name);

        let instd = body.instantiate(Some(&swapped_lc).into_iter());
        let doc = Doc::from("let")
                  .concat_space(self.pp_just_binder(&swapped_lc.lc_binding()).group())
                  .concat_space(":=")
                  .concat_newline(self.pp_expr(val).maybe_surround(0).group())
                  .concat("in")
                  .group()
                  .nest(self.pp_options.indent)
                  .concat_newline(self.pp_expr(&instd).maybe_surround(0)).group()
                  .as_parenable(0);
        self.ctx_mgr.remove_lc(&fresh_lc_name);
        doc
   }


    pub fn pp_just_binder(&self, binding : &Binder) -> Doc {
        self.pp_name(&binding.pp_name)
        .concat_space(":")
        .concat_newline(self.pp_expr(&binding.type_).maybe_surround(1).group())
    }


    pub fn pp_expr(&self, _e : &Expr) -> Parenable {
        //if !self.pp_options.proofs && self.ctx_mgr.tc.borrow_mut().is_proof(_e) {
        if !self.pp_options.proofs && _e.is_proof(&mut *self.ctx_mgr.tc.borrow_mut()).0 {
            Doc::from("_").as_parenable_max()
        } else {
            match _e.as_ref() {
                Var { dbj, .. } => Parenable::new_max(format!("#{}", dbj).into()),
                Sort { level, .. } => self.pp_sort_core(level),
                Const { name, levels, .. } => self.pp_const_core(name, levels.as_ref()),
                App { .. } => self.pp_app_core(_e),
                Local { binder, .. } => Parenable::new_max(self.pp_name(&binder.pp_name)),
                | Lambda { .. }
                | Pi { .. } => {
                    let (instd, binders) = self.parse_binders(_e);
                    let new_inner = self.pp_expr(&instd);
                    let new_result = self.pp_binders(binders.as_slice(), new_inner);
                    if self.pp_options.recycle_binder_names {
                        self.ctx_mgr.remove_lcs(&binders);
                    }
                    new_result
                }
                Let { binder, val, body, .. } => self.pp_let_core(binder, val, body),
            }
        }
    }


    pub fn main_def(&self, const_info : &ConstantInfo, val : &Expr) -> Doc {
        let (type_, binders) = self.parse_binders(&const_info.get_type());

        let mut slice_split_idx = 0usize;
        let mut val_cursor = val;
        // break loop when at least one of these three conditions is true :
        // 1. binders is exhausted
        // 2. val is no longer a Lambda
        // 3. is_forall(popped element) == false
        for elem in binders.iter() {
            match val_cursor.as_ref() {
                Lambda { body, .. } if elem.is_forall() => {
                    slice_split_idx += 1;
                    val_cursor = body;
                },
                _ => break
            }
        }

        let (params_slice, binders_slice) = binders.split_at(slice_split_idx);
        let instd = val_cursor.instantiate(params_slice.into_iter().rev().map(|x| &x.lc));

        let is_prop = const_info.get_type().is_proposition(&mut *self.ctx_mgr.tc.borrow_mut());
        let cmd = match is_prop {
            true => "lemma",
            false => "def"
        };

        let pp_val = match is_prop && !self.pp_options.proofs {
            true => Doc::from("_"),
            false => self.pp_expr(&instd).maybe_surround(0).group()
        };

        // This is the {u v} thing that shows the in-scope universes.
        let new_telescoped = self.telescope(Some(self.pp_name(const_info.get_name())), params_slice);


        let sub_doc_new = word_wrap_val(new_telescoped.into_iter())
                          .group()
                          .nest(self.pp_options.indent)
                          .concat_space(":")
                          //.concat_newline(self.pp_binders(binders_slice, self.pp_expr(&type_)).maybe_surround(0).group())
                          .concat_space(self.pp_binders(binders_slice, self.pp_expr(&type_)).maybe_surround(0).group())
                          .concat_space(":=");
        
        let result = Doc::from(cmd)
                     //.concat(self.get_ups(declar))
                     .concat(self.get_ups(const_info))
                     .concat_space(sub_doc_new.group().nest(self.pp_options.indent))
                     .concat_newline(pp_val)
                     .concat(Doc::line());

        if self.pp_options.recycle_binder_names {
            self.ctx_mgr.remove_lcs(&binders);
        }

        result
    }


    pub fn main_axiom(&self, const_info : &ConstantInfo) -> Doc {
        let (instd, binders) = self.parse_binders(&const_info.get_type());
        let doc = {
            let (prms, rst) = take_while_slice(binders.as_slice(), |x| x.is_forall()); 
            let telescoped = self.telescope(Some(self.pp_name(const_info.get_name())), prms);
            let sub_doc_new = word_wrap_val(telescoped.into_iter())
                              .concat_space(":")
                              .concat_newline(self.pp_binders(rst, self.pp_expr(&instd)).maybe_surround(0).group())
                              .group()
                              .nest(self.pp_options.indent);
            Doc::from("axiom")
            .concat(self.get_ups(const_info))
            .concat_space(sub_doc_new)
            .concat(Doc::line())
        };

        if self.pp_options.recycle_binder_names {
            self.ctx_mgr.remove_lcs(&binders);
        }

        doc
        // NOTE : At the moment the `builtin` tags are disabled.
        //        Add this as a configuration option.
        //if (self.pp_options.tag_builtins && declar.builtin) {
        //    Doc::from("/- builtin -/").concat_space(doc)
        //} else {
        //    doc
        //}
    }

    //pub fn pp_main(&self, declar : &DeclarationKind) -> Doc {
    pub fn pp_main(&self, const_info : &ConstantInfo) -> Doc {
        // FIXME eventually this will need to have
        // extra branches for `theorem` and `mutual`
        // If the consta_info item has a `value` level expression,
        // display it as a definition.
       match const_info.get_value_option() {
            Some(val) => self.main_def(const_info, &val),
            None => self.main_axiom(const_info)
        }

    }


    pub fn render_expr(&self, e : &Expr) -> String {
        self.pp_expr(e).doc.group().render(80)
    }


    //pub fn get_ups(&self, declar : &DeclarationKind) -> Doc {
    pub fn get_ups(&self, const_info : &ConstantInfo) -> Doc {
        match const_info.get_lparams() {
            v if v.is_empty() => Doc::nil(),
            v => Doc::from(" ").concat(self.pp_levels(v))
        }
    }


    /*
            Pi          ctx = []                     Pi        ctx = [a_1]
          /   \                                    /   \
        a      Pi                  =>             b      Pi
              /  \                                      /  \
            b     Pi                                   c    E
                /   \
              c      E
              
        let binder' = Binder(fresh(a), a.type_.instantiate(ctx.rev())).as_local()

        Continue up to ctx = [a_1, b_1, c_1] (where x_1 is fresh(x))

        let E' = E.instantiate(ctx.rev())

        (E', ctx)
    */
    pub fn parse_binders(&self, _e : &Expr) -> (Expr, Vec<ParsedBinder>) {
        let mut cursor = _e;
        let mut ctx = Vec::<ParsedBinder>::new();

        while let | Pi { binder, body, .. }
                  | Lambda { binder, body, .. } = cursor.as_ref() {
            let new_name = self.ctx_mgr.fresh_name(&binder.pp_name);
            let new_dom_ty = binder.type_.instantiate(ctx.iter().rev().map(|pb| &pb.lc));
            let new_dom = Binder::mk(new_name, new_dom_ty, binder.style);
            let new_local = new_dom.as_local();
            let new_parsed_binder = ParsedBinder::new(cursor.as_ref().is_pi(),
                                                      has_var(body, 0),
                                                      binder.pp_name.is_anon(),
                                                      new_local);
            ctx.push(new_parsed_binder);
            cursor = body;
        }
        let instd = cursor.instantiate(ctx.iter().rev().map(|pb| &pb.lc));
        (instd, ctx)
    }


}


pub fn print_declar(env : &ArcEnv, n : &Name, options : Option<PPOptions>) -> String {
    let declar = match env.read().constant_infos.get(n) {
        Some(d) => d.clone(),
        None => return String::new()
    };

    let pp = PrettyPrinter::new(env.clone(), options);

    pp.pp_main(&declar)
      .group()
      .render(pp.pp_options.width)
}

pub fn print_all(env : &ArcEnv, options : Option<PPOptions>) -> IoResult<()> {
    let handle = std::io::stdout();
    let mut _l = std::io::BufWriter::new(handle.lock());
    let options = options.unwrap_or(PPOptions::new_default());
    for const_info in env.read().constant_infos.values() {
        
        let pp = PrettyPrinter::new(env.clone(), Some(options));
        let _s = pp.pp_main(const_info)
                   .group()
                   .render(options.width);
        _l.write(_s.as_bytes())?;
    }
    _l.flush()
}

//#[derive(Clone)]
pub struct CtxMgr {
    pub used_lc_names : RefCell<HashSet<Name>>,
    pub tc : RefCell<TypeChecker>,
    pub incr_w_underscores : bool,
    // pub paren_mgr : Vec<T>

}
impl CtxMgr {
    pub fn new(env : ArcEnv, incr_w_underscores : bool) -> Self {
        CtxMgr {
            used_lc_names : RefCell::new(HashSet::with_capacity(50)),
            tc : RefCell::new(TypeChecker::new(Some(true), env.clone())),
            incr_w_underscores
        }
    }

    pub fn lookup_notation(&self, name : &Name) -> Option<Notation> {
        self.tc.borrow().env.read().notations.get(name).cloned()
    }

    // *** The only outward-facing function for this type ***
    // Returns a name known to not be in use by any other expression.
    // If the original suggested name is known to be conflict-free, returns
    // the base suggestion, else add a suffix until a conflict-free name
    // resembling the original suggestion is found.
    pub fn fresh_name(&self, suggestion : &Name) -> Name {
        // Remove non-word characters (IE regex \w)
        let sanitized = self.sanitize_name(suggestion);

        // Either make sure the sanitized name is conflict-free,
        // Or make one that is.
        let fresh = if self.already_used(&sanitized) {
            self.get_unused(&sanitized, 0)
        } else {
            sanitized
        };

        // Record the fact that this name is now in use.
        self.used_lc_names.borrow_mut().insert(fresh.clone());
        return fresh
    }

    // Predicate indicating whether a name is currently 'in-use' by
    // some other expression. Checks the local contxt currently known
    // to the CtxMgr, and also checks the overall environment in order
    // to reject variable names like `eq.rec` that would clash with
    // declared items.
    fn already_used(&self, n : &Name) -> bool {
        self.used_lc_names.borrow().contains(n) 
        || self.tc.borrow().env.read().constant_infos.get(n).is_some()
    }


    // Filter a name's characters with the equivalent of a regex `\w`.
    // If this filter returns the empty name, try to use a default
    // of "a".
    fn sanitize_name(&self, n : &Name) -> Name {
        let as_string = format!("{}", n);
        let filtered = as_string.chars()
                                .filter(|c| c.is_alphanumeric() || *c == '_')
                                .skip_while(|c| c.is_digit(10) || *c == '_')
                                .collect::<String>();
        if filtered.is_empty() {
            Name::from("a")
        } else {
            return Name::from(filtered.as_str())
        }
    }

    // Add a suffix, and increment said suffix until finding
    // a name known to be conflict-free.
    fn get_unused(&self, base : &Name, idx : usize) -> Name {
        let n = if self.incr_w_underscores {
            Name::from(format!("{}_{}", base, idx).as_str())
        } else {
            Name::from(format!("{}{}", base, idx).as_str())
        };
        if self.already_used(&n) {
            self.get_unused(base, idx + 1)
        } else {
            n
        }
    }

    pub fn is_implicit(&self, fun : &Expr) -> bool {
        let _x = fun.unchecked_infer(&mut *self.tc.borrow_mut());
        if let Pi { binder, .. } = _x.whnf(&mut *self.tc.borrow_mut()).as_ref() {
            !(binder.is_explicit())
        } else {
            false
        }
    }




    // If the pp_option `recycle_binder_names` is set to `true`, 
    // inform the CtxMgr that some name has gone out of scope, and
    // is no longer 'in use'/can be recycled by another expression.
    fn remove_lc(&self, target : &Name) {
        self.used_lc_names.borrow_mut().remove(target);
    }

    // execute `remove_lc` for a list of binders.
    fn remove_lcs(&self, binders : &Vec<ParsedBinder>) {
        for elem in binders.into_iter().rev() {
            self.used_lc_names.borrow_mut().remove(&elem.lc.lc_binding().pp_name);
        }
    }
}


#[derive(Clone, Copy)]
pub struct PPOptions {
    pub all : bool,
    pub implicit : bool,
    pub notation : bool,
    pub proofs : bool,
    pub locals_full_names : bool,
    pub indent : usize,
    pub width : usize,
    pub tag_builtins : bool,
    pub incr_w_underscores : bool,
    pub recycle_binder_names : bool,
}


impl PPOptions {
    pub fn new_all_false() -> Self {
        PPOptions {
            all : false,
            implicit : false,
            notation : false,
            proofs : false,
            locals_full_names : false,
            indent : 2usize,
            width : 80usize,
            tag_builtins : false,
            incr_w_underscores : false,
            // 
            recycle_binder_names : false,
        }
    }

    pub fn new_default() -> Self {
        PPOptions {
            all : false,
            implicit : false,
            notation : true,
            proofs : true,
            locals_full_names : false,
            indent : 2usize,
            width : 80usize,
            tag_builtins : false,
            incr_w_underscores : false,
            recycle_binder_names : true,
        }
    }
}



#[derive(Debug, Clone, PartialEq)]
pub struct ParsedBinder {
    pub is_pi : bool,
    pub occurs_in_body : bool,
    pub is_anon : bool,
    pub lc : Expr,
}

impl ParsedBinder {
    pub fn new(is_pi : bool, 
               occurs_in_body : bool, 
               is_anon : bool, 
               lc : Expr) -> Self {
        
        ParsedBinder {
            is_pi,
            occurs_in_body,
            is_anon,
            lc,
        }
    }

    // FIXME all of these methods have some issues I think, in terms
    // of how they determine implicits.
    pub fn is_imp(&self) -> bool {
        self.is_pi 
        && self.lc.lc_binding().style == BinderStyle::Default 
        && self.is_anon 
        && !self.occurs_in_body
    }

    pub fn is_forall(&self) -> bool {
        self.is_pi && !self.is_imp()
    }

    pub fn is_lambda(&self) -> bool {
        !self.is_pi
    }

    pub fn style(&self) -> BinderStyle {
        self.lc.lc_binding().style
    }

    pub fn type_(&self) -> &Expr {
        &self.lc.lc_binding().type_
    }

    pub fn name(&self) -> &Name {
        &self.lc.lc_binding().pp_name
    }
}


// See whether or not an expression's tree contains a variable
// whose DeBrujin index matches `dbj_key`. 
pub fn has_var(e : &Expr, dbj_key : usize) -> bool {
    if e.var_bound() as usize <= dbj_key {
        return false
    }
    match e.as_ref() {
        Var { dbj, .. } => *dbj == dbj_key,
        App { fun : a, arg : b, .. } => has_var(a, dbj_key) || has_var(b, dbj_key),
        Lambda { binder, body, .. } => has_var(&binder.type_, dbj_key) || has_var(body, dbj_key + 1),
        Pi { binder, body, .. } => has_var(&binder.type_, dbj_key) || has_var(body, dbj_key + 1),
        Let { binder, val, body, .. } => has_var(&binder.type_, dbj_key) || has_var(val, dbj_key) || has_var(body, dbj_key + 1),
        _ => unreachable!()
    }
}

// FIXME I think now that slice_patterns is stable, you won't
// need this anymore
// same as iterator's `take_while` function, but for a slice.
// takes a slice `s` and a predicate <T> -> bool `f`, returning
// ([elems for which f is true], [elems for which f is false])
pub fn take_while_slice<T>(s : &[T], f : impl Fn(&T) -> bool) -> (&[T], &[T]) {
    let mut idx = 0usize;
    while idx < s.len() && f(&s[idx]) {
        idx += 1
    }
    let lhs = &s[0..idx];
    let rhs = &s[idx..];
    (lhs, rhs)
}