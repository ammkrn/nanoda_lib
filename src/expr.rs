use crate::name::{ NamePtr, NamesPtr };
use crate::level::{ LevelPtr, LevelsPtr };
use crate::env::{ Declar::*, ReducibilityHint::* };
use crate::utils::{ 
    IsCtx, 
    IsLiveCtx, 
    List::*, 
    Ptr, 
    ListPtr, 
    Store,
    Env, 
    LiveZst, 
    HasNanodaDbg 
};

pub type ExprPtr<'a> = Ptr<'a, Expr<'a>>;
pub type ExprsPtr<'a> = ListPtr<'a, Expr<'a>>;


use Expr::*;
use BinderStyle::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalSerial(pub u64);


pub fn safe_pred(n : u16) -> u16 {
    if n == 0 {
        n
    } else {
        n - 1
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderStyle {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expr<'a> {
    Var { 
        dbj : u16
    },
    Sort {
        level : LevelPtr<'a>,
    },
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
    },
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        var_bound : u16,
        locals : bool,
    },
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial
    }

}


impl<'a> Expr<'a> {
    pub fn insert_env<'e>(self, env : &mut Env<'e>, live : &Store<LiveZst>) -> ExprPtr<'e> {
        let r = match self {
            Var { dbj } => <ExprPtr>::new_var(dbj, env),
            Sort { level } => level.insert_env(env, live).new_sort(env),
            Const { name, levels } => {
                let name = name.insert_env(env, live);
                let levels = levels.insert_env(env, live);
                <ExprPtr>::new_const(name, levels, env)
            },
            App { fun, arg, .. } => {
                let fun = fun.insert_env(env, live);
                let arg = arg.insert_env(env, live);
                fun.new_app(arg, env)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_pi(b_name, b_type, b_style, body, env)
            },
            Lambda { b_name, b_type, b_style, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_lambda(b_name, b_type, b_style, body, env)
            },
            Let { b_name, b_type, b_style, val, body, .. } => {
                let b_name = b_name.insert_env(env, live);
                let b_type = b_type.insert_env(env, live);
                let val = val.insert_env(env, live);
                let body = body.insert_env(env, live);
                <ExprPtr>::new_let(b_name, b_type, b_style, val, body, env)
            },
            // In combination with the assertion the `new_local` constructor
            // effectively ban Locals from the environment, ensuring that
            // contexts cannot be confused.
            Local {..} => unreachable!("Locals are not allowed in the environment!"),
        };
        assert!(r.in_env());
        r
    }    
}


impl<'a> ExprPtr<'a> {
    // This is for testing only.
    pub fn eq_mod_locals(self, other : Self, ctx : &impl IsCtx<'a>) -> bool {
        match (self.read(ctx), other.read(ctx)) {
            _ if self == other => true,
            (Var {..}, Var{..})
            | (Sort {..}, Sort {..})
            | (Const {..}, Const {..}) => self == other,
            (App { fun:f1, arg:a1, ..}, App { fun:f2, arg:a2, .. }) => {
                f1.eq_mod_locals(f2, ctx)
                &&
                a1.eq_mod_locals(a2, ctx)
            },
            | (Pi { b_type:t1, body:b1, .. }, Pi { b_type:t2, body:b2, .. }) 
            | (Lambda { b_type:t1, body:b1, .. }, Lambda { b_type:t2, body:b2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
                && b1.eq_mod_locals(b2, ctx)
            }
            (Let { b_type:t1, val:v1, body:b1, .. }, 
             Let { b_type:t2, val:v2, body:b2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
                && v1.eq_mod_locals(v2, ctx)
                && b1.eq_mod_locals(b2, ctx)
            }
            (Local { b_type:t1, .. }, Local { b_type:t2, .. }) => {
                t1.eq_mod_locals(t2, ctx)
            },
            _ => false
        }
    }

    pub fn var_bound(self, ctx : &impl IsCtx<'a>) -> u16 {
        match self.read(ctx) {
            Var { dbj } => (dbj + 1),
            | Sort {..} | Const {..} | Local {..} => 0,
            | App { var_bound, .. }
            | Pi { var_bound, ..} 
            | Lambda { var_bound, ..}
            | Let { var_bound, .. } => var_bound,
        }
    }

    pub fn has_locals(self, ctx : &impl IsCtx<'a>) -> bool {
        match self.read(ctx) {
            Var {..} => false,
            | Sort {..} | Const {..} => false,
            | App { locals, .. }
            | Pi { locals, ..} 
            | Lambda { locals, ..}
            | Let { locals, .. } => locals,
            | Local {..} => true
        }
    }


    pub fn try_const_info(self, ctx : &impl IsLiveCtx<'a>) -> Option<(NamePtr<'a>, LevelsPtr<'a>)> {
        match self.read(ctx) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None
        }
    }


    pub fn telescope_size(self, ctx : &impl IsCtx<'a>) -> u16 {
        match self.read(ctx) {
            Pi { body, .. } => 1 + body.telescope_size(ctx),
            _ => 0
        }
    }

    pub fn local_serial_infal(self, ctx : &impl IsLiveCtx<'a>) -> LocalSerial {
        match self.read(ctx) {
            Local { serial, .. } => serial,
            _ => panic!("can't take serial of a non-local expr")
        }
    }

    pub fn local_type_infal(self, ctx : &impl IsCtx<'a>) -> Self {
        match self.read(ctx) {
            Local { b_type, .. } => b_type,
            _ => panic!("Can't take local type from non-local!")
        }
    }

    pub fn new_var(dbj : u16, ctx : &mut impl IsCtx<'a>) -> Self {
        Var { dbj }.alloc(ctx)
    }

    pub fn new_const(
        name : NamePtr<'a>, 
        levels : LevelsPtr<'a>, 
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Const {
            name,
            levels
        }.alloc(ctx)
    }

    pub fn new_app(self, arg : Self, ctx : &mut impl IsCtx<'a>) -> Self {
        App {
            fun : self,
            arg,
            var_bound : self.var_bound(ctx).max(arg.var_bound(ctx)),
            locals : self.has_locals(ctx) || arg.has_locals(ctx),
        }.alloc(ctx)
    }

    pub fn new_pi(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Pi {
            b_name,
            b_type,
            b_style,
            body,
            var_bound : b_type.var_bound(ctx).max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx)
        }.alloc(ctx)
    }    

    pub fn new_lambda(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        Lambda {
            b_name,
            b_type,
            b_style,
            body,
            var_bound : b_type.var_bound(ctx).max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx)
        }.alloc(ctx)
    }
    
    pub fn new_let(
        b_name : NamePtr<'a>,
        b_type : Self,
        b_style : BinderStyle,
        val : Self,
        body : Self,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
          Let {
              b_name,
              b_type,
              b_style,
              val,
              body,
              var_bound : b_type.var_bound(ctx)
                          .max(val.var_bound(ctx))
                          .max(safe_pred(body.var_bound(ctx))),
            locals : b_type.has_locals(ctx) || body.has_locals(ctx) || val.has_locals(ctx)
        }.alloc(ctx)              
    }
    
    pub fn new_local(
        b_name : NamePtr<'a>, 
        b_type : Self,
        b_style : BinderStyle,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> ExprPtr<'a> {
        let l = Local {
            b_name,
            b_type,
            b_style,
            serial : ctx.next_local()
        }.alloc(ctx);
        assert!(!l.in_env());
        l
    }

    pub fn subst(self, ks : LevelsPtr<'a>, vs : LevelsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        fn subst_aux<'a>(e : ExprPtr<'a>, ks : LevelsPtr<'a>, vs : LevelsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
            if let Some(cached) = ctx.expr_cache().subst_cache.get(&(e, ks, vs)) {
                *cached
            } else {
                let r = match e.read(ctx) {
                    Var {..} => e,
                    Sort { level } => level.subst(ks, vs, ctx).new_sort(ctx),
                    Const { name, levels, .. } => {
                        <ExprPtr>::new_const(name, levels.subst_many(ks, vs, ctx), ctx)
                    },
                    App { fun, arg, .. } => {
                        let fun = subst_aux(fun, ks, vs, ctx);
                        let arg = subst_aux(arg, ks, vs, ctx);
                        <ExprPtr>::new_app(fun, arg, ctx)
                    },
                    Pi { b_name, b_type, b_style, body, .. } => {
                        let b_type = subst_aux(b_type, ks, vs, ctx);
                        let body   = subst_aux(body, ks, vs, ctx);
                        <ExprPtr>::new_pi(b_name, b_type, b_style, body, ctx)
                    }
                    Lambda { b_name, b_type, b_style, body, .. } => {
                        let b_type = subst_aux(b_type, ks, vs, ctx);
                        let body   = subst_aux(body, ks, vs, ctx);
                        <ExprPtr>::new_lambda(b_name, b_type, b_style, body, ctx)
                    }
                    Let { b_name, b_type, b_style, val, body, .. } => {
                        let b_type = subst_aux(b_type, ks, vs, ctx);
                        let val    = subst_aux(val, ks, vs, ctx);
                        let body   = subst_aux(body, ks, vs, ctx);
                        <ExprPtr>::new_let(b_name, b_type, b_style, val, body, ctx)
                    },
                    Local { b_name, b_type, b_style, .. } => {
                        let b_type = subst_aux(b_type, ks, vs, ctx);
                        <ExprPtr>::new_local(b_name, b_type, b_style, ctx)
                    }
                };

                ctx.expr_cache().subst_cache.insert((e, ks, vs), r);
                r
            }
        }

        // There's technically no reason this has to be cleared.
        // Saves some time.
        //ctx.expr_cache().subst_cache.clear();

        subst_aux(self, ks, vs, ctx)

    }       

    // Has (hopefully) the intuitive interface of from `f.foldl_apps([a, b, c])`
    // returning (((f a) b) c)
    pub fn foldl_apps(self, apps : ExprsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        match apps.read(ctx) {
            Nil => self,
            Cons(hd, tl) => self.new_app(hd, ctx).foldl_apps(tl, ctx)
        }
    }

    // Takes just the function (f) from `unfold_apps`. Slightly more efficient than
    // `unfold_apps().0` since we don't do anything with the list.
    pub fn unfold_apps_fun(self, ctx : &impl IsLiveCtx<'a>) -> Self {
        match self.read(ctx) {
            App { fun, .. } => fun.unfold_apps_fun(ctx),
            _ => self
        }
    }


    // Performs the opposite of foldl_apps; from `(((f a) b) c)`, produces
    // `(f, [a, b, c])`.
    pub fn unfold_apps(self, ctx : &mut impl IsLiveCtx<'a>) -> (Self, ExprsPtr<'a>) {
        fn unfold_apps_aux<'a>(e : ExprPtr<'a>, sink : ExprsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> (ExprPtr<'a>, ExprsPtr<'a>) {
            match e.read(ctx) {
                App { fun, arg, .. } => unfold_apps_aux(fun, Cons(arg, sink).alloc(ctx), ctx),
                _ => (e, sink)
            }
        }
        unfold_apps_aux(self, Nil::<Expr>.alloc(ctx), ctx)
    }      

    
    pub fn calc_height(self, ctx : &mut impl IsLiveCtx<'a>) -> u16 {
        pub fn calc_height_aux<'a>(e : ExprPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> u16 {
            if let Some(cached) = ctx.expr_cache().height_cache.get(&e) {
                *cached
            } else {
                let r = match e.read(ctx) {
                    Const { name, .. } => match ctx.get_declar(&name) {
                        Some(Definition { hint : Reg(n), .. }) => n,
                        _ => 0
                    },
                    App { fun, arg, .. } => {
                        calc_height_aux(fun, ctx)
                        .max(calc_height_aux(arg, ctx))
                    },
                    | Pi { b_type, body, .. }
                    | Lambda { b_type, body, .. } => {
                        calc_height_aux(b_type, ctx)
                        .max(calc_height_aux(body, ctx))
                    },
                    Let { b_type, val, body, .. } => {
                        calc_height_aux(b_type, ctx)
                        .max(calc_height_aux(val, ctx))
                        .max(calc_height_aux(body, ctx))
                    },
                    Var {..} | Sort {..} => 0,
                    Local {..} => panic!("calc_height should never receive a Local!"),
                };
                ctx.expr_cache().height_cache.insert(e, r);
                r
            }
        }

        ctx.expr_cache().height_cache.clear();
        calc_height_aux(self, ctx) + 1
    }



    pub fn abstr1(self, local : ExprPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        let l = Cons(local, Nil::<Expr>.alloc(ctx)).alloc(ctx);
        self.abstr(l, ctx)
    }

    pub fn abstr(self, locals : ExprsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
        fn abstr_aux<'a>(e : ExprPtr<'a>, locals : ExprsPtr<'a>, offset : u16, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
            if !e.has_locals(ctx) {
                e
            } else if let Some(cached) = ctx.expr_cache().abstr_cache.get(&(e, offset)) {
                *cached
            } else {
                let calcd = match e.read(ctx) {
                    Local {..} => locals.pos(e, ctx)
                                  .map(|pos| <ExprPtr>::new_var(pos as u16 + offset, ctx))
                                  .unwrap_or(e),
                    App { fun,  arg, .. } => {
                        let fun = abstr_aux(fun, locals, offset, ctx);
                        let arg = abstr_aux(arg, locals, offset, ctx);
                        <ExprPtr>::new_app(fun, arg, ctx)
                    },
                    Pi { b_name, b_type, b_style, body, .. } => {
                        let b_type = abstr_aux(b_type, locals, offset, ctx);
                        let body = abstr_aux(body, locals, offset + 1, ctx);
                        <ExprPtr>::new_pi(b_name, b_type, b_style, body, ctx)
                    }
                    Lambda { b_name, b_type, b_style, body, .. } => {
                        let b_type = abstr_aux(b_type, locals, offset, ctx);
                        let body = abstr_aux(body, locals, offset + 1, ctx);
                        <ExprPtr>::new_lambda(b_name, b_type, b_style, body, ctx)
                    }
                    Let { b_name, b_type, b_style, val, body, .. } => {
                        let b_type = abstr_aux(b_type, locals, offset, ctx);
                        let val = abstr_aux(val, locals, offset, ctx);
                        let body = abstr_aux(body, locals, offset + 1, ctx);
                        <ExprPtr>::new_let(b_name, b_type, b_style, val, body, ctx)
                    }
                    _ => unreachable!()
                };
    
                ctx.expr_cache().abstr_cache.insert((e, offset), calcd);
                calcd
            }
        }        
    
        if !self.has_locals(ctx) {
            self
        } else {
            ctx.expr_cache().abstr_cache.clear();
            abstr_aux(self, locals, 0u16, ctx)
        }
    }        
    
    pub fn inst1(self, subst : ExprPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        let l = Cons(subst, Nil::<Expr>.alloc(ctx)).alloc(ctx);
        self.inst(l, ctx)
    }

    pub fn inst(self, substs : ExprsPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        fn inst_aux<'a>(e : ExprPtr<'a>, substs : ExprsPtr<'a>, offset : u16, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
            if e.var_bound(ctx) <= offset {
                e
            } else if let Some(cached) = ctx.expr_cache().inst_cache.get(&(e, offset)) {
                *cached
            } else {
                let calcd = match e.read(ctx) {
                    Var { dbj } => substs.get((dbj as usize) - (offset as usize), ctx).unwrap_or(e),
                    App { fun,  arg, .. } => {
                        let fun = inst_aux(fun, substs, offset, ctx);
                        let arg = inst_aux(arg, substs, offset, ctx);
                        fun.new_app(arg, ctx)
                    },
                    Pi { b_name, b_type, b_style, body, .. } => {
                        let b_type = inst_aux(b_type, substs, offset, ctx);
                        let body = inst_aux(body, substs, offset + 1, ctx);
                        <ExprPtr>::new_pi(b_name, b_type, b_style, body, ctx)
                    }
                    Lambda { b_name, b_type, b_style, body, .. } => {
                        let b_type = inst_aux(b_type, substs, offset, ctx);
                        let body = inst_aux(body, substs, offset + 1, ctx);
                        <ExprPtr>::new_lambda(b_name, b_type, b_style, body, ctx)
                    }
                    Let { b_name, b_type, b_style, val, body, .. } => {
                        let b_type = inst_aux(b_type, substs, offset, ctx);
                        let val = inst_aux(val, substs, offset, ctx);
                        let body = inst_aux(body, substs, offset + 1, ctx);
                        <ExprPtr>::new_let(b_name, b_type, b_style, val, body, ctx)
                    }
                    _ => unreachable!()
                };
                ctx.expr_cache().inst_cache.insert((e, offset), calcd);
                calcd
            }
        }            

        if self.var_bound(ctx) == 0 {
            self
        } else {
            ctx.expr_cache().inst_cache.clear();
            inst_aux(self, substs, 0u16, ctx)
        }
    }        

    /*
    The very specific task this does is, given an expression `E` and a list
    of names `NS`, recursively search through `E` for a `Const { name, levels }`
    `C`, whose name is ANY of the names in `NS`. If such a `C` exists,
    return true, else return false.

    This is used in the formation of inductive types, to determine whether 
    a type is recursive, reflexive, contains only positive occurrences, and
    has only valid applications.
    */
    pub fn has_ind_occ(self, haystack : NamesPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        
        fn find_aux<'a>(e : ExprPtr<'a>, haystack : NamesPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> bool {
            if let Some(cached) = ctx.expr_cache().find_cache.get(&e) {
                *cached
            } else {
                let r = match e.read(ctx) {
                    Var {..} | Sort {..} => false,
                    Const { name, .. } => haystack.mem(name, ctx),
                    App { fun, arg, .. } => find_aux(fun, haystack, ctx)
                                          || find_aux(arg, haystack, ctx),
                    | Pi { b_type, body, .. }
                    | Lambda { b_type, body, .. } => find_aux(b_type, haystack, ctx)
                                                   || find_aux(body, haystack, ctx),
                    | Let { b_type, val, body, .. } => find_aux(b_type, haystack, ctx)
                                                    || find_aux(val, haystack, ctx)
                                                    || find_aux(body, haystack, ctx),
                    | Local { b_type, .. } => find_aux(b_type, haystack, ctx)
                };
                ctx.expr_cache().find_cache.insert(e, r);
                r
            }
        }

        find_aux(self, haystack, ctx)
    }    

    pub fn apply_pi(self, body : Self, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        match self.read(ctx) {
            Local { b_name, b_type, b_style, .. } => {
                let body = body.abstr1(self, ctx);
                <ExprPtr>::new_pi(b_name, b_type, b_style, body, ctx)
            },
            _ => unreachable!("Cannot apply pi with non-local domain type!")
        }
    }

    pub fn apply_lambda(self, body : Self, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        match self.read(ctx) {
            Local { b_name, b_type, b_style, .. } => {
                let body = body.abstr1(self, ctx);
                <ExprPtr>::new_lambda(b_name, b_type, b_style, body, ctx)
            },
            _ => unreachable!("Cannot apply lambda with non-local domain type!")
        }
    }    
}

fn fmt_binder<'a>(b_name : NamePtr<'a>, b_type : ExprPtr<'a>, b_style : BinderStyle, ctx : &impl IsCtx<'a>) -> String {
    let b_name = b_name.nanoda_dbg(ctx);
    let b_type = b_type.nanoda_dbg(ctx);
    match b_style {
        Default => {
            format!("({} : {})", b_name, b_type)
        },
        Implicit => {
            format!("{{{} : {}}}", b_name, b_type)

        },
        StrictImplicit => {
            format!("{{{{{} : {}}}}}", b_name, b_type)

        },
        InstImplicit => {
            format!("[{} : {}]", b_name, b_type)

        }
    }
}

impl<'a> HasNanodaDbg<'a> for Expr<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        match self {
            Var { dbj } => format!("Var{}", dbj),
            Sort { level } => format!("Sort {}", level.nanoda_dbg(ctx)),
            Const { name, levels } => {
                let name = name.nanoda_dbg(ctx);
                let levels = levels.nanoda_dbg(ctx);
                format!("Const ({}, {})", name, levels)
            }
            App { fun, arg, .. } => {
                let fun = fun.nanoda_dbg(ctx);
                let arg = arg.nanoda_dbg(ctx);
                format!("App ({}, {})", fun, arg)
            },
            Pi { b_name, b_type, b_style, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                format!("Π {}, ({})", binder, body)
            }
            Lambda { b_name, b_type, b_style, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                format!("λ {}, ({})", binder, body)
            }
            Let { b_name, b_type, b_style, val, body, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let body = body.nanoda_dbg(ctx);
                let val = val.nanoda_dbg(ctx);
                format!("Let {} := {} in {}", binder, val, body)
            },
            Local { b_name, b_type, b_style, serial, .. } => {
                let binder = fmt_binder(b_name, b_type, b_style, ctx);
                let serial = match serial {
                    LocalSerial(n) => n
                };

                format!("ser({}) of {}", serial, binder)
            }
        }
    }
}

impl<'a> ExprsPtr<'a> {
    // `self` is the list of domains/binders. Applies such that arguments
    // ([A, B, C], E) would make (Pi A : _, (Pi B : _, (Pi C : _, E)))
    pub fn fold_pis(self, body : ExprPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
        match self.read(ctx) {
            Cons(hd, tl) => {
                let inner = tl.fold_pis(body, ctx);
                hd.apply_pi(inner, ctx)
            },
            Nil => body
        }
    }

    pub fn fold_lambdas(self, body : ExprPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> ExprPtr<'a> {
        match self.read(ctx) {
            Cons(hd, tl) => {
                let inner = tl.fold_lambdas(body, ctx);
                hd.apply_lambda(inner, ctx)
            },
            Nil => body
        }
    }

}