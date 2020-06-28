use crate::utils::{ IsCtx, List::*, Live, HasNanodaDbg };
use crate::name::{ NamePtr, NamesPtr, Name} ;
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle::* };
use crate::env::{ Declar, DeclarPtr, RecRule, RecRulePtr, RecRulesPtr }; 
use crate::tc::infer::InferFlag::*;
use crate::trace::steps::*;
use crate::trace::IsTracer;
use crate::name;

#[derive(Debug)]
pub struct IndBlock<'a> {
    uparams : LevelsPtr<'a>,
    num_params : u16,
    nums_indices : Vec<u16>,
    pub ind_names : NamesPtr<'a>,
    ind_types : ExprsPtr<'a>,
    nums_cnstrs : Vec<u16>,
    cnstr_names : NamesPtr<'a>,
    cnstr_types : ExprsPtr<'a>,
    is_unsafe : bool,

    local_params    : Option<ExprsPtr<'a>>,
    local_indices   : Option<ExprsPtr<'a>>,
    ind_consts      : Option<ExprsPtr<'a>>,
    block_codom     : Option<LevelPtr<'a>>,
    use_dep_elim    : Option<bool>,
    is_nonzero      : Option<bool>,

    elim_level : Option<LevelPtr<'a>>,
    k_target : Option<bool>,
    majors : Option<ExprsPtr<'a>>,
    motives : Option<ExprsPtr<'a>>,
    minors : Option<ExprsPtr<'a>>,
    rec_rules : Option<RecRulesPtr<'a>>,
}

impl<'a> IndBlock<'a> {
    fn block_codom(&self) -> LevelPtr<'a> {
        self.block_codom.expect("Block codom has not been set yet!")
    }

    fn local_params(&self) -> ExprsPtr<'a> {
        self.local_params.expect("Block local params have not been set yet!")
    }


    fn local_indices(&self) -> ExprsPtr<'a> {
        self.local_indices.expect("Local rec indices have not been set yet!")
    }

    fn ind_consts(&self) -> ExprsPtr<'a> {
        self.ind_consts.expect("ind_consts have not been set yet!")
    }

    fn use_dep_elim(&self) -> bool {
        self.use_dep_elim.expect("use_dep_elim has not been set yet!")
    }

    fn is_nonzero(&self) -> bool {
        self.is_nonzero.expect("is_nonzero has not been set yet!")
    }

    fn elim_level(&self) -> LevelPtr<'a> {
        self.elim_level.expect("elim_level has not been set yet!")
    }
    
    fn k_target(&self) -> bool {
        self.k_target.expect("k_target has not been set yet!")
    }

    fn majors(&self) -> ExprsPtr<'a> {
        self.majors.expect("majors has not been set yet!")
    }

    fn motives(&self) -> ExprsPtr<'a> {
        self.motives.expect("motives has not been set yet!")
    }

    fn minors(&self) -> ExprsPtr<'a> {
        self.minors.expect("minors has not been set yet!")
    }

    fn rec_rules(&self) -> RecRulesPtr<'a> {
        self.rec_rules.expect("rec_rules has not been set yet!")
    }
    

    pub fn new(
        num_params : u16,
        nums_indices : Vec<u16>,
        uparams : LevelsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        nums_cnstrs : Vec<u16>,
        cnstr_names : NamesPtr<'a>,
        cnstr_types : ExprsPtr<'a>,
        is_unsafe : bool,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        assert_eq!(*&nums_cnstrs[0] as usize, cnstr_names.len(ctx).0);
        IndBlock {
            num_params,
            nums_indices,
            uparams,
            ind_names,
            ind_types,
            nums_cnstrs,
            cnstr_names,
            cnstr_types,
            is_unsafe,
            local_params : None,
            local_indices : None,
            ind_consts : None,
            block_codom : None,
            use_dep_elim : None,
            is_nonzero : None,
            elim_level : None,
            k_target : None,
            majors  : None,
            motives : None,
            minors  : None,
            rec_rules : None,
        }
    }
}

/*
// This only needs to be executed once for the whole block, since all
// of the mutuals share the same type parameters.
pub fn mk_local_params<'l, 'e : 'l>(
    rem_params : u16,
    ind_type : ExprPtr<'l>,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> (ExprsPtr<'l>, Step<MkLocalParamsZst>) {
    match ind_type.read(ctx) {
        Pi { b_name, b_type, b_style, body, .. } if rem_params != 0 => {
            let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
            let (body_prime, h1) = body.inst1(local, ctx);
            let (sink, h2) = mk_local_params(rem_params - 1, body_prime, ctx);
            MkLocalParams::Step {
                rem_params,
                n : b_name,
                t : b_type,
                s : b_style,
                b : body,
                serial : local.local_serial_infal(ctx),
                b_prime : body_prime,
                sink,
                h1,
                h2,
                ind_arg2 : ind_type,
                ind_arg3 : Cons(local, sink).alloc(ctx)
            }.step(ctx)
        },
        _ => {
            MkLocalParams::Base {
                rem_params,
                ind_type,
                ind_arg3 : Nil::<Expr>.alloc(ctx)
            }.step(ctx)
        }
    }
}

// Collect a list [top -> bottom] of Locals created from each 
// inductive type's indices AFTER instantiating with the block param locals
pub fn mk_local_indices1<'l, 'e : 'l>(
    ind_type_cursor : ExprPtr<'l>,
    rem_params : ExprsPtr<'l>,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> (ExprsPtr<'l>, Step<MkLocalIndices1Zst>) {
    match (ind_type_cursor.read(ctx), rem_params.read(ctx)) {
        (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl)) => {
            let (body_prime, h1) = body.inst1(hd, ctx);
            let (sink, h2) = mk_local_indices1(body_prime, tl, ctx);
            MkLocalIndices1::StepParam {
                n : b_name,
                t : b_type,
                s : b_style,
                b : body,
                b_prime : body_prime,
                local_param : hd,
                local_params : tl,
                local_indices : sink,
                h1,
                h2,
                ind_arg1 : self,
                ind_arg2 : rem_params,
            }.step(ctx)
        },
        (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
            let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx); 
            let (body_prime, h1) = body.inst1(local, ctx);
            let (sink, h2) = mk_local_indices1(body_prime, rem_params, ctx);
            let ind_arg3 = Cons(local, sink).alloc(ctx);
            MkLocalIndices1::StepIndex {
                n : b_name,
                t : b_type,
                s : b_style,
                b : body,
                serial : local.local_serial_infal(ctx),
                b_prime : body_prime,
                sink,
                h1,
                h2,
                ind_arg1 : self,
                ind_arg2 : rem_params,
                ind_arg3 : Cons(local, sink).alloc(ctx)
            }.step(ctx)
        },
        _ => {
            let (b, h1) = ind_type_cursor.is_pi(ctx);
            assert!(!b);
            MkLocalIndices1::Base {
                e : ind_type_cursor,
                h1,
                ind_arg2 : rem_params,
                ind_arg3 : Nil::<Expr>.alloc(ctx)
            }.step(ctx)
        }
    }
}

fn mk_local_indices_aux<'l, 'e : 'l>(
    rem_ind_types : ExprsPtr<'l>,
    local_params : ExprsPtr<'l>,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> (ExprsPtr<'l>, Step<MkLocalIndicesAuxZst>) {
    match rem_ind_types.read(ctx) {
        Cons(hd, tl) => {
            let sink = mk_local_indices_aux(tl, local_params, ctx);
            let hd = mk_local_indices1(hd, local_params, ctx); 
            hd.concat(sink, ctx)
        },
        Nil => Nil::<Expr>.alloc(ctx)
    }
}

impl<'l, 'e : 'l> IndBlock<'l> {
    // Conditions are 
    // 1. non-mutual
    // 2. is prop
    // 3. has only one constructor
    // 4. the constructor has zero arguments.
    // The main example is eq; it's an inductive prop
    // with one constructor (eq.refl), where eq.refl
    // takes zero arguments (the second `a` is just a re-use of the
    // parameter (a : A), and not a constructor argument.)
    pub fn init_k_target(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        unimplemented!()
        //let k_target = if self.ind_types.len(live) > 1 {
        //    false
        //} else if !self.block_codom().is_zero(live) {
        //    false
        //} else if self.cnstr_types.len(live) != 1 {
        //    false
        //} else {
        //    let only_cnstr = self.cnstr_types.get(0, live).expect("Failed to get checked `0` elem in init_k_target");
        //    self.init_k_target_aux(only_cnstr, self.num_params, live)
        //};

        //self.k_target = Some(k_target);
    }

    // Checks whether the constructor has 0 arguments by checking
    // whether the telescope with the block params removed is still
    // a Pi.
    pub fn init_k_target_aux(
        &self, 
        cnstr_cursor : ExprPtr<'l>, 
        rem_params : u16, 
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        unimplemented!()
        //match cnstr_cursor.read(live) {
        //    Pi { body, .. } if rem_params != 0 => self.init_k_target_aux(body, rem_params - 1, live),
        //    Pi {..} => false,
        //    _ => {
        //        assert_eq!(rem_params, 0);
        //        true
        //    }
        //}
    }        
}
*/

// This only needs to be executed once for the whole block, since all
// of the mutuals share the same type parameters.
pub fn mk_local_params<'l, 'e : 'l>(
    rem_params : u16,
    ind_type : ExprPtr<'l>,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> ExprsPtr<'l> {
    match ind_type.read(ctx) {
        Pi { b_name, b_type, b_style, body, .. } if rem_params != 0 => {
            let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
            let body = body.inst1(local, ctx).0;
            let sink = mk_local_params(rem_params - 1, body, ctx);
            Cons(local, sink).alloc(ctx)
        },
        _ => Nil::<Expr>.alloc(ctx)
    }
}

// Collect a list [top -> bottom] of Locals created from each 
// inductive type's indices AFTER instantiating with the block param locals
pub fn mk_local_indices1<'l, 'e : 'l>(
    ind_type_cursor : ExprPtr<'l>,
    rem_params : ExprsPtr<'l>,
    live : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> ExprsPtr<'l> {
    match (ind_type_cursor.read(live), rem_params.read(live)) {
        (Pi { body, .. }, Cons(hd, tl)) => {
            let body = body.inst1(hd, live).0;
            mk_local_indices1(body, tl, live)
        },
        (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
            let local = <ExprPtr>::new_local(b_name, b_type, b_style, live); 
            let body = body.inst1(local, live).0;
            let sink = mk_local_indices1(body, rem_params, live);
            Cons(local, sink).alloc(live)
        },
        _ => Nil::<Expr>.alloc(live)
    }
}

fn mk_local_indices_aux<'l, 'e : 'l>(
    rem_ind_types : ExprsPtr<'l>,
    local_params : ExprsPtr<'l>,
    live : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> ExprsPtr<'l> {
    match rem_ind_types.read(live) {
        Cons(hd, tl) => {
            let sink = mk_local_indices_aux(tl, local_params, live);
            let hd = mk_local_indices1(hd, local_params, live); 
            hd.concat(sink, live).0
        },
        _ => Nil::<Expr>.alloc(live)
    }
}

fn is_valid_ind_app_cond3<'l, 'e : 'l>(
    cnstr_apps : ExprsPtr<'l>,
    local_params : ExprsPtr<'l>,
    ctx : &Live<'l, 'e, impl 'e + IsTracer>
) -> bool {
    match (cnstr_apps.read(ctx), local_params.read(ctx)) {
        (Cons(x, xs), Cons(y, ys)) if x == y => is_valid_ind_app_cond3(xs, ys, ctx),
        (_, Nil) => true,
        _ => unreachable!("failed is_valid_ind_app_cond3 for ind")
    }
}

impl<'l, 'e : 'l> IndBlock<'l> {
    pub fn get_codom_univ(
        &self,
        ind_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> LevelPtr<'l> {
        match (ind_type_cursor.read(ctx), rem_params.read(ctx)) {
            (Pi { body, .. }, Cons(_, tl)) => self.get_codom_univ(body, tl, ctx),
            (Pi { body, .. }, Nil) => self.get_codom_univ(body, rem_params, ctx),
            (_, Nil) => ind_type_cursor.ensure_sort(&mut ctx.as_tc(Some(self.uparams), None)).0,
            _ => unreachable!("Cannot run out of telescope space with params left to go!")
        }
    }


    
    // Checking involves the following :
    // 1. ensuring that the type parameters of all inductives being declare in a block are the same
    // 2. ensuring that the result is a valid Sort.
    // 3. ensuring that the result level of all inductives being declared in a block are equal.
    #[allow(unconditional_recursion)]
    fn check_ind_type(
        &self, 
        ind_name : NamePtr<'l>,
        ind_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprPtr<'l> {
        match (ind_type_cursor.read(ctx), rem_params.read(ctx)) {
            (Pi { b_type, body, .. }, Cons(hd, tl)) => {
                let local_type = hd.local_type_infal(ctx);
                b_type.assert_def_eq(local_type, &mut ctx.as_tc(Some(self.uparams), None));
                let body = body.inst1(hd, ctx).0;
                self.check_ind_type(ind_name, body, tl, ctx)
            },
            (Pi { body, .. }, Nil) => self.check_ind_type(ind_name, body, rem_params, ctx),
            (_, Nil) => {
                // This is done "again" because we need to ensure that all items in the block
                // have the same codomain universe.
                {
                    let mut tc = ctx.as_tc(Some(self.uparams), None);
                    let codom_level = ind_type_cursor.ensure_sort(&mut tc).0;
                    assert!(codom_level.try_eq_antisymm(self.block_codom(), &mut tc).0);
                }
                <ExprPtr>::new_const(ind_name, self.uparams, ctx)
                //let codom_level = ind_type_cursor.ensure_sort(&mut ctx.as_tc(Some(self.uparams), None)).0;
                //assert!(codom_level.eq_antisymm(self.block_codom(), ctx).0);
                //<ExprPtr>::new_const(ind_name, self.uparams, ctx)
            },
            _ => unreachable!("ind::check got an invalid pattern (Pi nil, or non-pi Cons)")
        }
    }            

    pub fn declare_ind_type1(
        &self,
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprPtr<'l> {
        let ind_const = self.check_ind_type(ind_name, ind_type, self.local_params(), ctx);
        let ind = <DeclarPtr>::new_inductive(
            ind_name,
            self.uparams,
            ind_type,
            self.num_params,
            self.ind_names,
            self.cnstr_names,
            self.is_unsafe,
            ctx
        );
       ctx.admit_declar(ind);
       ind_const
    }

    pub fn declare_ind_types_aux(
        &mut self,
        rem_names : NamesPtr<'l>,
        rem_types : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match (rem_names.read(ctx), rem_types.read(ctx)) {
            (Cons(n, ns), Cons(t, ts)) if ns.len(ctx).0 > 0 => {
                // Recurse first
                let ind_const_sink = self.declare_ind_types_aux(ns, ts, ctx);
                //
                let ind_const = self.declare_ind_type1(n, t, ctx);
                Cons(ind_const, ind_const_sink).alloc(ctx)
            },
            (Cons(n, ns), Cons(t, ts)) => {
                assert_eq!(ns.len(ctx).0, 0);
                assert_eq!(ts.len(ctx).0, 0);
                // This just executes the (Nil, Nil) branch for logging.
                let sink = self.declare_ind_types_aux(ns, ts, ctx);
                //
                let local_params = mk_local_params(self.num_params, t, ctx);
                let codom_level = self.get_codom_univ(t, local_params, ctx);

                let use_dep_elim = codom_level.maybe_nonzero(ctx).0;

                let is_nonzero = codom_level.is_nonzero(ctx).0;

                self.local_params = Some(local_params);
                self.block_codom  = Some(codom_level);
                self.use_dep_elim = Some(use_dep_elim);
                self.is_nonzero   = Some(is_nonzero);
                let ind_const = self.declare_ind_type1(n, t, ctx);

                Cons(ind_const, sink).alloc(ctx)
            }
            (Nil, Nil) => Nil::<Expr>.alloc(ctx),
            _ => unreachable!("unequal lengths @ `declare_ind_types_aux`")
        }
    }    

    pub fn declare_ind_types(&mut self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let ind_consts = self.declare_ind_types_aux(self.ind_names, self.ind_types, ctx);
        self.ind_consts = Some(ind_consts);
    }    

    /*
    Valid ind app :
    Condition 1 : 
        The base `Const(..)` obtained by unfolding is the ind_const for the constructor's
        parent inductive. IE `list.cons` for some type `A : Type u` has to end with
        an application of `Const("list", [u])` to some arguments.
    Condition 2 : 
        The number of arguments that the constructor applies to the base `Const(..)` 
        khas to be equal to the number of block_params + the number
        of indices for the given inductive type.
        It has to be equal to their sum because we're dealing with the internal
        representation. In surface Lean we're used to just applying a number
        of arguments equal to the number of indices.
    Condition 3:
        assert that the first arguments being applied to the base `Const(..)`
        in any given constructor are exactly the parameters required by the block.
        In surface lean, we're used to just giving indices, but pretend everything
        has an `@` prefix.
        IE
        {A : Sort u}
        for `@eq.refl A a a
        unfolds as (Const(eq, [u]), [A, a, a])
    */
    pub fn is_valid_ind_app(
        &self,
        parent_ind_type : ExprPtr<'l>,
        parent_ind_const : ExprPtr<'l>,
        stripped_cnstr_type : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        let (base_const, base_apps) = stripped_cnstr_type.unfold_apps(ctx).0;
        let cond1 = base_const == parent_ind_const;
        let cond2 = base_apps.len(ctx).0 == parent_ind_type.telescope_size(ctx).0 as usize;

        if ((!cond1) || (!cond2)) {
            false
        } else {
            let cond3 = is_valid_ind_app_cond3(base_apps, self.local_params(), ctx);
            cond1 && cond2 && cond3
        }
    }    

    pub fn which_valid_ind_app_aux(
        &self,
        rem_ind_types : ExprsPtr<'l>,
        rem_ind_consts : ExprsPtr<'l>,
        u_i_ty : ExprPtr<'l>,
        ind_ty_index : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> u16 {
        match (rem_ind_types.read(ctx), rem_ind_consts.read(ctx)) {
            (Cons(t, _), Cons(c, _)) if self.is_valid_ind_app(t, c, u_i_ty, ctx) => ind_ty_index,
            (Cons(_, ts), Cons(_, cs)) => self.which_valid_ind_app_aux(ts, cs, u_i_ty, 1 + ind_ty_index, ctx),
            _ => unreachable!("All applications must contain a valid use for SOME inductive datatype being declared")
        }
    }        

    pub fn which_valid_ind_app(
        &self,
        u_i_ty : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> u16 {
        self.which_valid_ind_app_aux(self.ind_types, self.ind_consts(), u_i_ty, 0, ctx)
    }

    pub fn is_rec_argument(
        &self, 
        parent_ind_type : ExprPtr<'l>,
        parent_ind_const : ExprPtr<'l>,
        cnstr_btype_cursor : ExprPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        let cnstr_btype_cursor = cnstr_btype_cursor.whnf(&mut live.as_tc(Some(self.uparams), None)).0;
        match cnstr_btype_cursor.read(live) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, live);
                self.is_rec_argument(parent_ind_type, parent_ind_const, body.inst1(local, live).0, live)

            },
            _ => self.is_valid_ind_app(parent_ind_type, parent_ind_const, cnstr_btype_cursor, live)
        }
    }        


    // This is only ONE of the binders from the constructor's telescope,
    // AFTER the block params have been removed. These are essentially
    // the "extra arguments" to the constructor.
    // When we match here on Pi { x, y }, `x` is the left hand side
    // of a function argument to an inductive constructor.
    // We need to search `y` to prevent non-positive occurrences like
    // | mk (f : A -> A -> thing A) : thing A
    fn check_positivity1(
        &self,
        parent_ind_type : ExprPtr<'l>,
        parent_ind_const : ExprPtr<'l>,
        cnstr_type_cursor : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) {

        let cnstr_type_cursor = cnstr_type_cursor.whnf(&mut ctx.as_tc(Some(self.uparams), None)).0;

        match cnstr_type_cursor.read(ctx) {
            _ if !cnstr_type_cursor.has_ind_occ(self.ind_names, ctx).0 => (),
            Pi { b_type, .. } if b_type.has_ind_occ(self.ind_names, ctx).0 => panic!("non-positive occurrence!"),
            Pi { b_name, b_type, b_style, body, .. } => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let body = body.inst1(local, ctx).0;
                self.check_positivity1(parent_ind_type, body, parent_ind_const, ctx)
            },
            // assertion-like
            _ => assert!(self.is_valid_ind_app(parent_ind_type, parent_ind_const, cnstr_type_cursor, ctx))
        }
    }    

    // Basically `true`; log a message here
    fn check_positivity_is_unsafe(&self) {
        assert!(self.is_unsafe)
    }
    


    // This always begins with the full type/param list
    pub fn check_cnstr1(
        &self,
        parent_ind_type : ExprPtr<'l>,
        parent_ind_const : ExprPtr<'l>,
        cnstr_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) {
        match (cnstr_type_cursor.read(ctx), rem_params.read(ctx)) {
            (Pi { b_type, body, .. }, Cons(hd, tl)) => {
                let param_type = hd.local_type_infal(ctx);
                b_type.assert_def_eq(param_type, &mut ctx.as_tc(Some(self.uparams), None));
                let body = body.inst1(hd, ctx).0;

                self.check_cnstr1(parent_ind_type, parent_ind_const, body, tl, ctx)
            },
            (Pi { b_type, .. }, Nil) => {
                
                // assertion that b_type is a well formed inhabitant of something.
                let s = b_type.ensure_type(&mut ctx.as_tc(Some(self.uparams), None)).0;

                if !(self.block_codom().is_zero(ctx).0 || s.leq(self.block_codom(), ctx).0) {
                    panic!("Constructor argument was too large for the corresponding inductive type!")
                }

                if self.is_unsafe {
                    self.check_positivity_is_unsafe();
                } else {
                    self.check_positivity1(parent_ind_type, parent_ind_const, b_type, ctx)
                }
            },
            _ => {
                assert!(self.is_valid_ind_app(parent_ind_type, parent_ind_const, cnstr_type_cursor, ctx))
            }
        }
    }    

    // The list is passed L -> R, IE [base, step1, step2]
    pub fn mk_cnstrs_group(
        &self,
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_cnstr_names : NamesPtr<'l>,
        rem_cnstr_types : ExprsPtr<'l>,
        cnstr_idx : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Vec<DeclarPtr<'l>> {
        match (rem_cnstr_names.read(ctx), rem_cnstr_types.read(ctx)) {
            (Cons(n, ns), Cons(t, ts)) => {
                // recurse first
                let mut sink = self.mk_cnstrs_group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    ns, 
                    ts, 
                    cnstr_idx + 1, 
                    ctx
                );
                // 

                // assertion.
                let _= self.check_cnstr1(ind_type, ind_const, t, self.local_params(), ctx);

                let this_cnstr = <DeclarPtr>::new_cnstr(
                    n, 
                    self.uparams, 
                    t, 
                    ind_name, 
                    cnstr_idx,
                    self.num_params, 
                    self.is_unsafe, 
                    ctx
                );

                sink.push(this_cnstr);
                sink
            },
            (Nil, Nil) => Vec::new(),
            _ => unreachable!("unequal lengths @ declare_cnstrs_group!")
        }


    }

    pub fn mk_cnstrs(
        &self,
        rem_ind_ns : NamesPtr<'l>,
        rem_ind_ts : ExprsPtr<'l>,
        rem_ind_cs : ExprsPtr<'l>,
        nums_cs : &[u16],
        rem_cnstr_ns : NamesPtr<'l>,
        rem_cnstr_ts : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Vec<DeclarPtr<'l>> {
        match (rem_ind_ns.read(ctx), rem_ind_ts.read(ctx), rem_ind_cs.read(ctx), nums_cs) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [num, nums @ ..]) => {
                let cn_hd = rem_cnstr_ns.take(*num as usize, ctx).0;
                let cn_tl = rem_cnstr_ns.skip(*num as usize, ctx).0;

                let ct_hd = rem_cnstr_ts.take(*num as usize, ctx).0;
                let ct_tl = rem_cnstr_ts.skip(*num as usize, ctx).0;
                let mut sink = self.mk_cnstrs(i_ns, i_ts, i_cs, nums, cn_tl, ct_tl, ctx);
                let hd = self.mk_cnstrs_group(i_n, i_t, i_c, cn_hd, ct_hd, 0, ctx);
                sink.extend(hd);
                sink
            },    
            (Nil, Nil, Nil, []) => Vec::new(),
            _ => unreachable!("Mismatch in lengths; inductive::mk_cnstrs")
        }
    }

    pub fn declare_cnstrs(&self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let all_cnstrs = self.mk_cnstrs(
            self.ind_names, 
            self.ind_types, 
            self.ind_consts(),
            self.nums_cnstrs.as_slice(),
            self.cnstr_names,
            self.cnstr_types,
            ctx
        );

        for d in all_cnstrs {
            ctx.admit_declar(d);
        }
    }    

    /*
    The pi binder types we collect after passing the parameters
    are NOT indices, they're just arguments.
    We know what the indices are, because they're the first 0 or more
    argumeents to the unfolded expression at the end.
    */
    #[allow(unconditional_recursion)]
    pub fn large_elim_test_aux(
        &self, 
        cnstr_type_cursor : ExprPtr<'l>,
        rem_params : u16,
        non_zero_cnstr_args : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        match cnstr_type_cursor.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } if rem_params != 0 => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let body = body.inst1(local, ctx).0;
                self.large_elim_test_aux(body, rem_params - 1, non_zero_cnstr_args, ctx)
            },
            // We're assembling a list of the binders that are known to NOT
            // be props/in Sort 0
            Pi { b_name, b_type, b_style, body, .. } => {
                assert_eq!(rem_params, 0);
                let b_type_level = b_type.ensure_type(&mut ctx.as_tc(Some(self.uparams), None)).0;
                let b_type_is_zero = b_type_level.is_zero(ctx).0;

                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let body = body.inst1(local, ctx).0;

                match b_type_is_zero {
                    // If the binder type is in Sort 0, just pass over it.
                    true => self.large_elim_test_aux(
                        body, 
                        rem_params, 
                        non_zero_cnstr_args,
                        ctx
                    ),
                    // If the binder type is NOT in sort 0, add it to the list
                    // of constructor args that need to be checked
                    false => self.large_elim_test_aux(
                        body,
                        rem_params,
                        Cons(local, non_zero_cnstr_args).alloc(ctx),
                        ctx
                    )
                }
            },
            _ => {
                assert_eq!(rem_params, 0);
                // In this context, args (the exprs being applied to the ind_const)
                // is the inductive block's params + the base type's indices
                let (_, args) = cnstr_type_cursor.unfold_apps(ctx).0;
                // if the list of non-prop constructor args is NOT a subset of
                // the exprs being applied to the inductive (which is params + indices)
                // then we can say that this type ONLY eliminates into Prop/Sort 0
                non_zero_cnstr_args.subset(args, ctx).0
            }
        }
    }

    // FIXME Control flow needs to be broken up here too.
    pub fn large_elim_test(
        &self, 
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        if self.is_nonzero() {
            true
        } else if self.ind_types.len(live).0 > 1 {
            false
        } else if self.cnstr_types.len(live).0 > 1 {
            false
        } else {
            match self.cnstr_types.get(0, live).0 {
                // has no constructors (is `false`, which can eliminate whever it wants)
                None => true,
                // At this point, we know that we're dealing with an inductive that...
                // 1. is not a mutual inductive
                // 2. is an inductive proposition (because its result sort is Prop/0)
                // 3. has one and only one constructor
                Some(only_cnstr) => self.large_elim_test_aux(
                    only_cnstr, 
                    self.num_params, 
                    Nil::<Expr>.alloc(live), 
                    live
                )
            }
        }
    }    

    pub fn gen_elim_level(&self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) -> LevelPtr<'l> {
        let mut i = 0u64;
        let base = name!("u", live);
        let mut p = base.new_param(live);

        while p.mem(self.uparams, live).0 {
        //while self.uparams.mem(p, live).0 {
            i += 1;
            p = base.new_num(i, live).new_param(live);
        }
        p
    }    

    pub fn mk_elim_level(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) { 
        let elim_level = if self.large_elim_test(live) {
            self.gen_elim_level(live)
        } else {
            Level::Zero.alloc(live)
        };

        self.elim_level = Some(elim_level);
    }    

    pub fn init_k_target(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {

        let k_target = if self.ind_types.len(live).0 > 1 {
            false
        } else if !self.block_codom().is_zero(live).0 {
            false
        } else if self.cnstr_types.len(live).0 != 1 {
            false
        } else {
            let only_cnstr = self.cnstr_types.get(0, live).0.expect("Failed to get checked `0` elem in init_k_target");
            self.init_k_target_aux(only_cnstr, self.num_params, live)
        };

        self.k_target = Some(k_target);
    }

    pub fn init_k_target_aux(
        &self, 
        cnstr_cursor : ExprPtr<'l>, 
        rem_params : u16, 
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> bool {
        match cnstr_cursor.read(live) {
            Pi { body, .. } if rem_params != 0 => self.init_k_target_aux(body, rem_params - 1, live),
            Pi {..} => false,
            _ => {
                assert_eq!(rem_params, 0);
                true
            }
        }
    }    


    pub fn mk_local_indices(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let local_indices = mk_local_indices_aux(self.ind_types, self.local_params(), live);
        self.local_indices = Some(local_indices);
    }

    pub fn mk_major1(
        &self, 
        ind_const : ExprPtr<'l>,
        local_indices : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprPtr<'l> {
        ind_const
        .foldl_apps(self.local_params(), live).0
        .foldl_apps(local_indices, live).0
    }    


    // These are 1 for 1 with the inductive types list;
    // also goes [A, B, C]
    // for types [A, B, C]
    pub fn mk_majors(
        &self, 
        nums_indices : &[u16],
        ind_consts : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match (nums_indices, ind_consts.read(live)) {
            ([num, nums @ ..], Cons(ic, ics)) => {
                let indices_hd = local_indices.take(*num as usize, live).0;
                let indices_tl = local_indices.skip(*num as usize, live).0;

                let sink = self.mk_majors(nums, ics, indices_tl, live);
                let t = name!("t", live);
                let major = <ExprPtr>::new_local(t, self.mk_major1(ic, indices_hd, live), Default, live);
                Cons(major, sink).alloc(live)
            },
            ([], Nil) => Nil::<Expr>.alloc(live),
            _ => unreachable!("Uneven lengths in mk_majors")
        }
    }        

    pub fn mk_majors_wrapper(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) { 
        let majors = self.mk_majors(
            self.nums_indices.as_slice(),
            self.ind_consts(), 
            self.local_indices(), 
            live
        );
        self.majors = Some(majors);
    }


    pub fn mk_motive_indep(
        &self,
        local_indices : ExprsPtr<'l>,
        ind_type_idx : u64,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprPtr<'l> {
        let motive_base = self.elim_level().new_sort(live);
        let motive_type = local_indices.fold_pis(motive_base, live).0;
        let motive_name = if self.ind_types.len(live).0 > 1 {
            name!("C", live).new_num(ind_type_idx, live)
        } else {
            name!("C", live)
        };

        <ExprPtr>::new_local(motive_name, motive_type, Implicit, live)
    }    

    pub fn mk_motive_dep(
        &self,
        local_indices : ExprsPtr<'l>,
        major : ExprPtr<'l>,
        ind_type_idx : u64,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprPtr<'l> {
        let motive_base = self.elim_level().new_sort(live);
        let motive_type = major.apply_pi(motive_base, live).0;
        let motive_type = local_indices.fold_pis(motive_type, live).0;
        let motive_name = if self.ind_types.len(live).0 > 1 {
            name!("C", live).new_num(ind_type_idx, live)
        } else {
            name!("C", live)
        };

        <ExprPtr>::new_local(motive_name, motive_type, Implicit, live)
    }


    // Motives (C) are 1 for 1 with ind types being declared. Also go L -> R.
    // Are numbered as IE [C.1, C.2, C.3]
    // for a list of inds [A, B, C]
    pub fn mk_motives(
        &self, 
        nums_indices : &[u16],
        majors : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        ind_type_idx : u64,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match (nums_indices, majors.read(live)) {
            ([num, nums @ ..], Cons(mj, mjs)) => {
                let indices_hd = local_indices.take(*num as usize, live).0;
                let indices_tl = local_indices.skip(*num as usize, live).0;

                let sink = self.mk_motives(nums, mjs, indices_tl, ind_type_idx + 1, live);
                let motive = if self.use_dep_elim() {
                    self.mk_motive_dep(indices_hd, mj, ind_type_idx, live)
                } else {
                    self.mk_motive_indep(indices_hd, ind_type_idx, live)
                };
                Cons(motive, sink).alloc(live)
            },
            ([], Nil) => Nil::<Expr>.alloc(live),
            _ => unreachable!("Uneven list lengths in mk_motives")
        }
    }        

    
    pub fn mk_motives_wrapper(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let motives = self.mk_motives(
            self.nums_indices.as_slice(),
            self.majors(), 
            self.local_indices(), 
            0u64, 
            live
        );
        self.motives = Some(motives);
    }

    pub fn get_i_indices(
        &self, 
        stripped_instd_cnstr_type : ExprPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (u16, ExprsPtr<'l>) {
        // Position in self.ind_types of the inductive type being applied/created
        // by the constructor
        let valid_app_idx = self.which_valid_ind_app(stripped_instd_cnstr_type, live);
        let (_, cnstr_args_wo_params) = stripped_instd_cnstr_type.unfold_apps(live).0;
        (valid_app_idx, cnstr_args_wo_params.skip(self.num_params as usize, live).0)
    }    

    // The main thing this does is make two lists, the one on the left is all of the 
    // constructor's arguments, and the one on the right is only the constructors arguments
    // that are recursive.
    pub fn strip_cnstr(
        &self, 
        ind_t : ExprPtr<'l>,
        ind_c : ExprPtr<'l>,
        cnstr_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprPtr<'l>, ExprsPtr<'l>, ExprsPtr<'l>) {
        match (cnstr_type_cursor.read(live), rem_params.read(live)) {
            (Pi { body, .. }, Cons(hd, tl)) => {
                let body = body.inst1(hd, live).0;
                let (inner, all_args, rec_args) = self.strip_cnstr(
                    ind_t, 
                    ind_c, 
                    body, 
                    tl, 
                    live
                );
                (inner, all_args, rec_args)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, live);
                let body = body.inst1(local, live).0;

                let (stripped, all_args, rec_args) = self.strip_cnstr(
                    ind_t, 
                    ind_c, 
                    body, 
                    rem_params, 
                    live
                );

                let all_args = Cons(local, all_args).alloc(live);
                let rec_args = if self.is_rec_argument(ind_t, ind_c, b_type, live) {
                    Cons(local, rec_args).alloc(live)
                } else {
                    rec_args
                };

                (stripped, all_args, rec_args)
            },
            _ => (cnstr_type_cursor, Nil::<Expr>.alloc(live), Nil::<Expr>.alloc(live))
        }
    }    

    // used by mk_minors and mk_rec_rules
    #[allow(unconditional_recursion)]
    pub fn handle_rec_args_aux(
        &self,
        rec_arg_cursor : ExprPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprPtr<'l>, ExprsPtr<'l>) {
        match rec_arg_cursor.read(live) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, live);
                let body = body.inst1(local, live).0.whnf(&mut live.as_tc(Some(self.uparams), None)).0;
                let (inner, sink) = self.handle_rec_args_aux(body, live);
                (inner, Cons(local, sink).alloc(live))
            },
            _ => (rec_arg_cursor, Nil::<Expr>.alloc(live))
        }
    }    
    
    pub fn handle_rec_args_minor(
        &self,
        rem_rec_args : ExprsPtr<'l>,
        self_idx2 : u16,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match rem_rec_args.read(live) {
            Nil => rem_rec_args,
            Cons(hd, tl) => {
                let sink = self.handle_rec_args_minor(tl, self_idx2 + 1, live);

                let u_i_ty = hd.infer(InferOnly, &mut live.as_tc(None, None)).0;
                let u_i_ty = u_i_ty.whnf(&mut live.as_tc(Some(self.uparams), None)).0;

                let (arg_ty, xs) = self.handle_rec_args_aux(u_i_ty, live);

                let (it_indices, noparam_apps) = self.get_i_indices(arg_ty, live);
                
                let motive = self.motives().get(it_indices as usize, live).0.expect("Failed to get specified motive(2)!");

                let motive_base = motive.foldl_apps(noparam_apps, live).0;

                let motive_base = if self.use_dep_elim() {
                    let u_app = hd.foldl_apps(xs, live).0;
                    motive_base.new_app(u_app, live)
                } else {
                    motive_base
                };

                let v_i_ty = xs.fold_pis(motive_base, live).0;
                let v_name = name!("v", live).new_num(self_idx2 as u64, live);
                let v_i = <ExprPtr>::new_local(v_name, v_i_ty, Default, live);
                Cons(v_i, sink).alloc(live)
            },
        }

    }

    pub fn mk_minors1group(
        &self, 
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_cnstr_names : NamesPtr<'l>,
        rem_cnstr_types : ExprsPtr<'l>,
        cnstr_idx : u64,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match (rem_cnstr_names.read(live), rem_cnstr_types.read(live)) {
            (Cons(c_n, c_ns), Cons(c_t, c_ts)) => {
                let sink = self.mk_minors1group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    c_ns, 
                    c_ts, 
                    cnstr_idx + 1, 
                    live
                );

                let (
                    stripd_instd_cnstr_type, 
                    all_args,
                    rec_args
                ) = self.strip_cnstr(
                    ind_type,
                    ind_const,
                    c_t,
                    self.local_params(),
                    live
                );

                let (cnstr_ind_type_pos, noparam_apps) = self.get_i_indices(stripd_instd_cnstr_type, live);
                

                let motive = self.motives().get(cnstr_ind_type_pos as usize, live).0.expect("Failed to get specified motive!");

                let c_app = motive.foldl_apps(noparam_apps, live).0;

                let c_app = if self.use_dep_elim() {
                    let rhs = <ExprPtr>::new_const(c_n, self.uparams, live)
                                     .foldl_apps(self.local_params(), live).0
                                     .foldl_apps(all_args, live).0;
                    c_app.new_app(rhs, live)
                } else {
                    c_app
                };

                let v = self.handle_rec_args_minor(rec_args, 0, live);

                let minor_type = v.fold_pis(c_app, live).0;
                let minor_type = all_args.fold_pis(minor_type, live).0;
                let minor_name = name!("m", live).new_num(cnstr_idx, live);
                let minor = <ExprPtr>::new_local(minor_name, minor_type, Default, live);

                Cons(minor, sink).alloc(live)
            },
            _ => Nil::<Expr>.alloc(live)

        }
    }        
    
    pub fn mk_minors(
        &self, 
        ins : NamesPtr<'l>,
        its : ExprsPtr<'l>,
        ics : ExprsPtr<'l>,
        nums_cnstrs : &[u16],
        cns : NamesPtr<'l>,
        cts : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match (ins.read(live), its.read(live), ics.read(live), nums_cnstrs) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [nc, ncs @ ..]) => {
                let cn_hd = cns.take(*nc as usize, live).0;
                let cn_tl = cns.skip(*nc as usize, live).0;

                let ct_hd = cts.take(*nc as usize, live).0;
                let ct_tl = cts.skip(*nc as usize, live).0;

                let sink = self.mk_minors(i_ns, i_ts, i_cs, ncs, cn_tl, ct_tl, live);
                let this = self.mk_minors1group(i_n, i_t, i_c, cn_hd, ct_hd, 1, live);
                this.concat(sink, live).0
            },
            (Nil, Nil, Nil, []) => Nil::<Expr>.alloc(live),
            _ => unreachable!()
        }
        
    }

    

    pub fn mk_minors_wrapper(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let x = self.mk_minors(
            self.ind_names, 
            self.ind_types, 
            self.ind_consts(), 
            self.nums_cnstrs.as_slice(),
            self.cnstr_names, 
            self.cnstr_types, 
            live
        );

        self.minors = Some(x);
    }    

    pub fn get_rec_levels(&self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) -> LevelsPtr<'l> {
        match self.elim_level().read(live) {
            Level::Param(..) => Cons(self.elim_level(), self.uparams).alloc(live),
            _ => self.uparams
        }
    }    
    

    /*
    L -> R orientation 
    */
    pub fn handle_rec_args_rec_rule(
        &self,
        ind_name : NamePtr<'l>,
        rem_rec_args : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ExprsPtr<'l> {
        match rem_rec_args.read(live) {
            Cons(hd, tl) => {
                let sink = self.handle_rec_args_rec_rule(ind_name, tl, live);

                let u_i_ty = hd.infer(InferOnly, &mut live.as_tc(None, None)).0;
                let u_i_ty = u_i_ty.whnf(&mut live.as_tc(Some(self.uparams), None)).0;

                let (u_i_ty, xs) = self.handle_rec_args_aux(u_i_ty, live);

                let (_, noparam_apps) = self.get_i_indices(u_i_ty, live);
                
                let rec_name = ind_name.new_str(format!("rec"), live);

                let rec_app = <ExprPtr>::new_const(rec_name, self.get_rec_levels(live), live);
                
                let app = rec_app.foldl_apps(self.local_params(), live).0;
                let app = app.foldl_apps(self.motives(), live).0;
                let app = app.foldl_apps(self.minors(), live).0;
                let app = app.foldl_apps(noparam_apps, live).0;

                let app_rhs = hd.foldl_apps(xs, live).0;
                let app = app.new_app(app_rhs, live);

                let v_hd = xs.fold_lambdas(app, live).0;

                Cons(v_hd, sink).alloc(live)
            },
            Nil => rem_rec_args
        }
    }    

    pub fn mk_rec_rule1(
        &self, 
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        cnstr_name : NamePtr<'l>,
        cnstr_type : ExprPtr<'l>,
        // vv The whole group of minors
        mnrs_grp : ExprsPtr<'l>,
        // vv minor corresponding to the constructor's index
        this_minor : ExprPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> RecRulePtr<'l> {
        let (_, all_args, rec_args) = self.strip_cnstr(ind_type,
                                                       ind_const,
                                                       cnstr_type,
                                                       self.local_params(),
                                                       live);
        
        let handled_rec_args = self.handle_rec_args_rec_rule(ind_name, rec_args, live);

        let comp_rhs = this_minor.foldl_apps(all_args, live).0
                                 .foldl_apps(handled_rec_args, live).0;
        let comp_rhs = all_args.fold_lambdas(comp_rhs, live).0;
        let comp_rhs = mnrs_grp.fold_lambdas(comp_rhs, live).0;
        let comp_rhs = self.motives().fold_lambdas(comp_rhs, live).0;
        let comp_rhs = self.local_params().fold_lambdas(comp_rhs, live).0;
        let num_fields = cnstr_type.telescope_size(live).0 - self.num_params;
        RecRule::new(cnstr_name, num_fields, comp_rhs).alloc(live)
    }    


    pub fn mk_rec_rules1group(
        &mut self,
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_cnstr_names : NamesPtr<'l>,
        rem_cnstr_types : ExprsPtr<'l>,
        mnr_grp : ExprsPtr<'l>,
        rem_minors : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> RecRulesPtr<'l> {
        match (rem_cnstr_names.read(live), rem_cnstr_types.read(live), rem_minors.read(live)) {
            (Cons(n, ns), Cons(t, ts), Cons(m, ms)) => {
                let sink = self.mk_rec_rules1group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    ns, 
                    ts, 
                    mnr_grp, 
                    ms, 
                    live
                );
                let this = self.mk_rec_rule1(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    n, 
                    t, 
                    mnr_grp, 
                    m, 
                    live
                );
                Cons(this, sink).alloc(live)
            },
            (Nil, Nil, Nil) => Nil::<RecRule>.alloc(live),
            _ => unreachable!("Uneven list lengths in mk_rec_rules1group")
        }

    }    


    // ind_names
    // ind_types
    // ind_consts
    // nums_cnstrs
    // cnstr_names
    // cnstr_types
    // minors
    pub fn mk_rec_rules(
        &mut self, 
        ins : NamesPtr<'l>,
        its : ExprsPtr<'l>,
        ics : ExprsPtr<'l>,
        nscs : &[u16],
        cns : NamesPtr<'l>,
        cts : ExprsPtr<'l>,
        mnrs : ExprsPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> RecRulesPtr<'l> {

        match (ins.read(live), its.read(live), ics.read(live), nscs) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [num, nums @ ..]) => {
                let cn_grp = cns.take(*num as usize, live).0;
                let cns_tl = cns.skip(*num as usize, live).0;

                let ct_grp = cts.take(*num as usize, live).0;
                let cts_tl = cts.skip(*num as usize, live).0;

                let mnr_grp = mnrs.take(*num as usize, live).0;
                let mnrs_tl = mnrs.skip(*num as usize, live).0;

                let sink = self.mk_rec_rules(
                    i_ns, 
                    i_ts, 
                    i_cs, 
                    nums, 
                    cns_tl, 
                    cts_tl, 
                    mnrs_tl, 
                    live
                );
                let hd_rrs = self.mk_rec_rules1group(
                    i_n, 
                    i_t, 
                    i_c, 
                    cn_grp, 
                    ct_grp, 
                    mnr_grp, 
                    mnr_grp, 
                    live
                );

                hd_rrs.concat(sink, live).0
            },

            (Nil, Nil, Nil, []) => Nil::<RecRule>.alloc(live),
            _ => unreachable!("Bad match in mk_rec_rules")

        }
    }    

    
    pub fn declare_rec_rules(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let rec_rules = self.mk_rec_rules(
            self.ind_names,
            self.ind_types,
            self.ind_consts(),
            self.nums_cnstrs.clone().as_slice(),
            self.cnstr_names,
            self.cnstr_types,
            self.minors(),
            live
        );

        self.rec_rules = Some(rec_rules);
    }    

    pub fn mk_recursor_aux(
        &self, 
        ind_name : NamePtr<'l>,
        num_indices : u16,
        motive : ExprPtr<'l>,
        major : ExprPtr<'l>,
        local_indices : ExprsPtr<'l>,
        minors : ExprsPtr<'l>,
        rec_rules : RecRulesPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> DeclarPtr<'l> {
        let num_minors = minors.len(live).0 as u16;
        let num_motives = self.motives().len(live).0 as u16;
        let rec_name = ind_name.new_str(format!("rec"), live);

        let motive_app_base = motive.foldl_apps(local_indices, live).0;
        let motive_app = if self.use_dep_elim() {
            motive_app_base.new_app(major, live)
        } else {
            motive_app_base
        };

        let rec_ty = major.apply_pi(motive_app, live).0;
        let rec_ty = local_indices.fold_pis(rec_ty, live).0;
        let rec_ty = minors.fold_pis(rec_ty, live).0;
        let rec_ty = self.motives().fold_pis(rec_ty, live).0;
        let rec_ty = self.local_params().fold_pis(rec_ty, live).0;
        let rec_uparams = self.get_rec_levels(live);
        let major_idx = self.num_params + num_indices + num_minors + num_motives;

        let r = <DeclarPtr>::new_recursor(
            rec_name,
            rec_uparams,
            rec_ty,
            self.ind_names,
            self.num_params,
            num_indices,
            self.motives().len(live).0 as u16,
            num_minors as u16,
            major_idx,
            rec_rules,
            self.k_target(),
            self.is_unsafe,
            live
        );



        r

    }    


    pub fn mk_recursor(
        &self, 
        ind_names : NamesPtr<'l>,
        nums_cnstrs : &[u16],
        nums_indices : &[u16],
        motives : ExprsPtr<'l>,
        majors : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        minors : ExprsPtr<'l>,
        rec_rules : RecRulesPtr<'l>,
        live : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Vec<DeclarPtr<'l>> {
        match (
            ind_names.read(live), 
            nums_cnstrs, 
            nums_indices, 
            motives.read(live), 
            majors.read(live)
        ) {
            (Cons(n, ns), 
             [num, nums @ ..], 
             [li, lis @ ..], 
             Cons(mo, mos), 
             Cons(ma, mas)) => {
                let mnr_hd = minors.take(*num as usize, live).0;
                let mnr_tl = minors.skip(*num as usize, live).0;

                let rr_hd = rec_rules.take(*num as usize, live).0;
                let rr_tl = rec_rules.skip(*num as usize, live).0;

                let indices_hd = local_indices.take(*li as usize, live).0;
                let indices_tl = local_indices.skip(*li as usize, live).0;

                // recurse
                let mut sink = self.mk_recursor(
                    ns, 
                    nums, 
                    lis, 
                    mos, 
                    mas, 
                    indices_tl, 
                    mnr_tl, 
                    rr_tl, 
                    live
                );

                let d = self.mk_recursor_aux(
                    n, 
                    *li,
                     mo, 
                     ma, 
                     indices_hd, 
                     mnr_hd, 
                     rr_hd, 
                     live
                );

                sink.push(d);
                sink
            },
            (Nil, [], [], Nil, Nil) => Vec::new(),
            _ => panic!("declare recursors must receive lists with equal lengths")
        }
    }

    pub fn declare_recursors(&mut self, live : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let recursors = self.mk_recursor(
            self.ind_names, 
            self.nums_cnstrs.as_slice(),
            self.nums_indices.as_slice(),
            self.motives(), 
            self.majors(), 
            self.local_indices(), 
            self.minors(), 
            self.rec_rules(),
            live
        );
        assert_eq!(self.cnstr_names.len(live).0, self.minors().len(live).0);
        assert_eq!(self.cnstr_names.len(live).0, self.rec_rules().len(live).0);
        assert_eq!(self.ind_types.len(live).0, recursors.len());

        for r in recursors {
            live.admit_declar(r);
        }
    }
}


