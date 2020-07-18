use crate::utils::{ IsCtx, List::*, Live, HasNanodaDbg };
use crate::name::{ NamePtr, NamesPtr, Name} ;
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle::* };
use crate::env::{ Declar, DeclarPtr, DeclarsPtr, RecRule, RecRulePtr, RecRulesPtr }; 
use crate::tc::infer::InferFlag::*;
use crate::trace::steps::*;
use crate::trace::{ IsTracer, items::HasTraceItem };
use crate::name;



#[derive(Debug, Clone, Copy)]
pub struct IndBlockPtr {
    pub ind_serial : u16,
}


#[derive(Debug, Clone, Copy)]
pub struct CheckedIndBlockPtr {
    pub ind_serial : u16,
}



#[derive(Debug, Clone)]
pub struct IndBlock<'a> {
    // This field is just for bookkeeping.
    pub ind_serial : u16,
    pub uparams : LevelsPtr<'a>,
    pub num_params : u16,
    pub nums_indices : Vec<u16>,
    pub ind_names : NamesPtr<'a>,
    pub ind_types : ExprsPtr<'a>,
    pub nums_ctors : Vec<u16>,
    pub ctor_names : NamesPtr<'a>,
    pub ctor_types : ExprsPtr<'a>,
    pub is_unsafe : bool,

    // All of these fields get added after `check_ind_types`
    pub local_params    : Option<ExprsPtr<'a>>,
    pub local_indices   : Option<ExprsPtr<'a>>,
    pub ind_consts      : Option<ExprsPtr<'a>>,
    pub block_codom     : Option<LevelPtr<'a>>,
    pub is_nonzero      : Option<(bool, Step<IsNonzeroZst>)>,
    pub is_zero : Option<(bool, Step<IsZeroZst>)>,
}


impl<'a> IndBlock<'a> {
    pub fn as_checked<'e>(self, ctx : &mut Live<'a, 'e, impl 'e + IsTracer>) -> CheckedIndblock<'a> {
        let checked = CheckedIndblock {
            indblock_ptr : self.as_ptr(),
            ind_serial : self.ind_serial,
            uparams : self.uparams,
            num_params : self.num_params,
            nums_indices : self.nums_indices,
            ind_names : self.ind_names,
            ind_types : self.ind_types,
            nums_ctors : self.nums_ctors,
            ctor_names : self.ctor_names,
            ctor_types : self.ctor_types,
            is_unsafe : self.is_unsafe,

            local_params : self.local_params.unwrap(),
            local_indices : self.local_indices.unwrap(),
            ind_consts : self.ind_consts.unwrap(),
            block_codom : self.block_codom.unwrap(),
            is_nonzero : self.is_nonzero.unwrap(),
            is_zero : self.is_zero.unwrap(),

            elim_level : None,
            k_target : None,
            majors : None,
            motives : None,
            minors : None,
            rec_rules : None
        };

        checked.trace_item(ctx);
        checked
    }

    pub fn block_codom(&self) -> LevelPtr<'a> {
        self.block_codom.expect("Block codom has not been set yet!")
    }

    pub fn local_params(&self) -> ExprsPtr<'a> {
        self.local_params.expect("Block local params have not been set yet!")
    }


    pub fn local_indices(&self) -> ExprsPtr<'a> {
        self.local_indices.expect("Local rec indices have not been set yet!")
    }

    pub fn ind_consts(&self) -> ExprsPtr<'a> {
        self.ind_consts.expect("ind_consts have not been set yet!")
    }

    pub fn is_nonzero(&self) -> (bool, Step<IsNonzeroZst>) {
        self.is_nonzero.expect("is_nonzero has not been set yet!")
    }

    pub fn is_zero(&self) -> (bool, Step<IsZeroZst>) {
        self.is_zero.expect("is_zero has not been set yet!")
    }

    fn as_ptr(&self) -> IndBlockPtr {
        IndBlockPtr {
            ind_serial : self.ind_serial,
        }
    }

    pub fn new(
        ind_serial : u16,
        num_params : u16,
        nums_indices : Vec<u16>,
        uparams : LevelsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        nums_ctors : Vec<u16>,
        ctor_names : NamesPtr<'a>,
        ctor_types : ExprsPtr<'a>,
        is_unsafe : bool,
        ctx : &mut impl IsCtx<'a>
    ) -> Self {
        assert_eq!(*&nums_ctors[0] as usize, ctor_names.len(ctx));
        let block = IndBlock {
            ind_serial,
            num_params,
            nums_indices,
            uparams,
            ind_names,
            ind_types,
            nums_ctors,
            ctor_names,
            ctor_types,
            is_unsafe,
            local_params : None,
            local_indices : None,
            ind_consts : None,
            block_codom : None,
            is_nonzero : None,
            is_zero : None,
        };

        block.trace_item(ctx);
        block
    }
}



pub struct CheckedIndblock<'a> {
    // This field is just for bookkeeping.
    indblock_ptr : IndBlockPtr,
    pub ind_serial : u16,
    pub uparams : LevelsPtr<'a>,
    pub num_params : u16,
    pub nums_indices : Vec<u16>,
    pub ind_names : NamesPtr<'a>,
    pub ind_types : ExprsPtr<'a>,
    pub nums_ctors : Vec<u16>,
    pub ctor_names : NamesPtr<'a>,
    pub ctor_types : ExprsPtr<'a>,
    pub is_unsafe : bool,

    // All of these fields get added after `check_ind_types`
    pub local_params    : ExprsPtr<'a>,
    pub local_indices   : ExprsPtr<'a>,
    pub ind_consts      : ExprsPtr<'a>,
    pub block_codom     : LevelPtr<'a>,
    pub is_nonzero      : (bool, Step<IsNonzeroZst>),
    pub is_zero : (bool, Step<IsZeroZst>),

    // These are not part of the output/struct since it wouldn't
    // yield enough benefit.
    elim_level : Option<(LevelPtr<'a>, Step<MkElimLevelZst>)>,
    k_target : Option<bool>,
    majors : Option<ExprsPtr<'a>>,
    motives : Option<ExprsPtr<'a>>,
    minors : Option<ExprsPtr<'a>>,
    rec_rules : Option<RecRulesPtr<'a>>,

}


impl<'a> CheckedIndblock<'a> {
    fn use_dep_elim(&self) -> bool {
        !(self.is_zero.0)
    }

    fn elim_level(&self) -> (LevelPtr<'a>, Step<MkElimLevelZst>) {
        self.elim_level.expect("elim_level not set yet")
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

    fn as_ptr(&self) -> CheckedIndBlockPtr {
        CheckedIndBlockPtr {
            ind_serial : self.ind_serial,
        }
    }
}


// This only needs to be executed once for the whole block, since all
// of the mutuals share the same type parameters.
pub fn mk_local_params<'l, 'e : 'l>(
    ind_type_cursor : ExprPtr<'l>,
    params_rem : u16,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> (ExprsPtr<'l>, Step<MkLocalParamsZst>) {
    match ind_type_cursor.read(ctx) {
        Pi { b_name, b_type, b_style, body, .. } if params_rem != 0 => {
            let params_hd = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
            let (b_prime, h1) = body.inst1(params_hd, ctx);
            let (params_tl, h2) = mk_local_params(b_prime, params_rem - 1, ctx);
            let params = Cons(params_hd, params_tl).alloc(ctx);
            MkLocalParams::Step {
                n : b_name,
                t : b_type,
                s : b_style,
                b : body,
                num_params : params_rem,
                serial : params_hd.local_serial_infal(ctx),
                b_prime,
                params_tl,
                params_hd,
                ind_type_cursor,
                num_params_prime : (params_rem - 1),
                params,
                h1,
                h2,
            }.step(ctx)
        },
        _ => {
            let params = Nil::<Expr>.alloc(ctx);
            MkLocalParams::Base {
                ind_type_cursor,
                num_params : params_rem,
                params
            }.step(ctx)
        }
    }
}



fn valid_param_apps<'l, 'e : 'l>(
    rem_ind_apps : ExprsPtr<'l>,
    rem_block_params : ExprsPtr<'l>,
    ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> (bool, Step<ValidParamAppsZst>) {
    match (rem_ind_apps.read(ctx), rem_block_params.read(ctx)) {
        (Cons(x, ind_apps_tl), Cons(y, block_params_tl)) if x == y => {
            let (b, h1) = valid_param_apps(ind_apps_tl, block_params_tl, ctx);
            ValidParamApps::Step {
                hd : x,
                ind_apps_tl,
                block_params_tl,
                rem_ind_apps,
                rem_block_params,
                b : (x == y) && b,
                h1,
            }.step(ctx)
        }
        (_, Nil) => {
            ValidParamApps::Base {
                rem_ind_apps,
                rem_block_params,
                b : true
            }.step(ctx)
        }
        (Nil, Cons(..)) => unreachable!("failed valid param apps; nil cons"),
        (Cons(x, _), Cons(y, _)) => {
            unreachable!(
                "Failed valid param apps with cons cons; lhs : {}\n rhs : {}\n",
                x.nanoda_dbg(ctx),
                y.nanoda_dbg(ctx),

            )
        }
        // => unreachable!("failed valid_param_apps")
    }
}

impl<'l, 'e : 'l> IndBlock<'l> {
     // Given one of the inductive types and the local_params,
    // returns the type's local_indices and codom_level as a pair,
    // while assergint that it has the right (same) params.
    // returns (local_indices, codom_level, ind_const)
    pub fn handle_telescope1(
        &self,
        i_n : NamePtr<'l>,
        ind_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ((ExprsPtr<'l>, LevelPtr<'l>, ExprPtr<'l>), Step<HandleTelescope1Zst>) {
        match (ind_type_cursor.read(ctx), rem_params.read(ctx)) {
            (Pi { b_name, b_type, b_style, body, .. }, Cons(params_hd, params_tl)) => {
                let t1 = params_hd.local_type_infal(ctx);
                let h1 = b_type.assert_def_eq(t1, &mut ctx.as_tc(None, None));
                let (b_prime, h2) = body.inst1(params_hd, ctx);
                let (result, h3) = self.handle_telescope1(i_n, b_prime, params_tl, ctx);
                HandleTelescope1::StepParam {
                    indblock : self.as_ptr(),
                    ind_name : i_n,
                    codom_level : result.1,
                    //
                    n : b_name,
                    t1,
                    t2 : b_type,
                    s : b_style,
                    b : body,
                    serial : params_hd.local_serial_infal(ctx),
                    params_tl,
                    b_prime,
                    result,
                    ind_type_cursor,
                    params_hd,
                    rem_params,
                    h1,
                    h2,
                    h3
                }.step(ctx)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
                let indices_hd = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h1) = body.inst1(indices_hd, ctx);
                let (rec_result, h2) = self.handle_telescope1(i_n, b_prime, rem_params, ctx);
                let (indices_tl, codom_level, ind_const) = rec_result;
                let result = (
                    Cons(indices_hd, indices_tl).alloc(ctx),
                    codom_level, 
                    ind_const
                );

                HandleTelescope1::StepIndex {
                    indblock : self.as_ptr(),
                    ind_name : i_n,
                    codom_level,
                    //
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    serial : indices_hd.local_serial_infal(ctx),
                    indices_tl,
                    b_prime,
                    //
                    ind_type_cursor,
                    rem_params,
                    indices_hd,
                    ind_const,
                    rec_result,
                    result,
                    h1,
                    h2
                }.step(ctx)
            },
            (..) => {
                let (b, h1) = ind_type_cursor.is_pi(ctx);
                assert!(!b);
                assert_eq!(rem_params.len(ctx), 0);
                
                let (codom_level, h2) = ind_type_cursor.ensure_sort(&mut ctx.as_tc(None, None));
                let local_indices = Nil::<Expr>.alloc(ctx);
                let ind_const = <ExprPtr>::new_const(i_n, self.uparams, ctx);
                let result = (local_indices, codom_level, ind_const);
                HandleTelescope1::Base {
                    indblock : self.as_ptr(),
                    ind_name : i_n,
                    codom_level,
                    ind_type_cursor,
                    rem_params,
                    ind_const,
                    result,
                    h1,
                    h2,
                }.step(ctx)
            }
        }
    }
    
    pub fn handle_telescopes(
        &self,
        params : ExprsPtr<'l>,
        rem_ind_names : NamesPtr<'l>,
        rem_ind_types : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ((ExprsPtr<'l>, LevelPtr<'l>, ExprsPtr<'l>), Step<HandleTelescopesZst>) {
        match (rem_ind_names.read(ctx), rem_ind_types.read(ctx)) {
            // Case where both elements only have one element remaining.
            (Cons(i_n, i_ns), Cons(i_t, i_ts)) if i_ts.read(ctx) == Nil => {
                assert_eq!(i_ns.read(ctx), Nil);
                let (rec_result, h1) = self.handle_telescope1(i_n, i_t, params, ctx);
                let (indices, codom_level, c) = rec_result;
                let result = (
                    indices,
                    codom_level, 
                    Cons(c, Nil::<Expr>.alloc(ctx)).alloc(ctx)
                );
                HandleTelescopes::Base {
                    indblock : self.as_ptr(),
                    params,
                    codom_level,
                    //
                    i_ns_hd : i_n,
                    i_ts_hd : i_t,
                    indices,
                    ind_const : c,
                    rec_result,
                    rem_ind_names,
                    rem_ind_types,
                    result,
                    h1,
                }.step(ctx)
            }
            (Cons(i_n, i_ns), Cons(i_t, i_ts)) => {
                let (rec_result, h1) = self.handle_telescopes(params, i_ns, i_ts, ctx);
                let (indices_r, codom_level, ind_cs_tl) = rec_result;

                let (hd_result, h2) = self.handle_telescope1(i_n, i_t, params, ctx);
                let (indices_l, codom_level2, ind_cs_hd) = hd_result;

                let ind_cs = Cons(ind_cs_hd, ind_cs_tl).alloc(ctx);

                let (levels_eq, h3) = codom_level.assert_eq_antisymm(codom_level2, ctx);
                assert!(levels_eq);

                let indices = indices_l.concat(indices_r, ctx);
                let result = (indices, codom_level, ind_cs);

                HandleTelescopes::Step {
                    indblock : self.as_ptr(),
                    params,
                    codom_level,
                    //
                    i_ns_hd : i_n,
                    i_ns_tl : i_ns,
                    i_ts_hd : i_t,
                    i_ts_tl : i_ts,
                    indices_r,
                    indices_l,
                    codom_level2,
                    ind_cs_tl,
                    ind_cs_hd,
                    ind_cs,
                    rec_result,
                    hd_result,
                    indices,
                    rem_ind_names,
                    rem_ind_types,
                    result,
                    h1,
                    h2,
                    h3,
                }.step(ctx)
            }
            _ => unreachable!("uneven list lengths in check_ind_types")
        }
    }   

    pub fn check_ind_types(
        &mut self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Step<CheckIndTypesZst> {

        let (i_t, i_ts, (params, h1)) = match self.ind_types.read(ctx) {
            Nil => unreachable!("Cannot check empty inductive block!"),
            Cons(i_t, i_ts) => (i_t, i_ts, mk_local_params(i_t, self.num_params, ctx)),
        };

        let (telescopes_result, h2) = self.handle_telescopes(
            params,
            self.ind_names,
            self.ind_types,
            ctx
        );
        let (indices, codom_level, ind_consts) = telescopes_result;

        let (is_nonzero, h4) = codom_level.is_nonzero(ctx);
        let (is_zero, h5) = codom_level.is_zero(ctx);
       
        self.local_params = Some(params);
        self.local_indices = Some(indices);
        self.block_codom  = Some(codom_level);
        self.is_nonzero = Some((is_nonzero, h4));
        self.is_zero = Some((is_zero, h5));
        self.ind_consts = Some(ind_consts);

        
        assert_eq!(params.len(ctx), self.num_params as usize);
        assert_eq!(ind_consts.len(ctx), self.ind_types.len(ctx));

        CheckIndTypes::Base {
            indblock : self.as_ptr(),
            params,
            indices,
            codom_level,
            ind_consts,
            ind_types_hd : i_t,
            ind_types_tl : i_ts,
            telescopes_result,
            h1,
            h2,
        }.step_only(ctx)
    }    


    // all of these arguments are diminishing.
    pub fn mk_ind_types(
        &self, 
        rem_ind_names : NamesPtr<'l>,
        rem_ind_types : ExprsPtr<'l>,
        rem_ctor_names : NamesPtr<'l>,
        rem_nums_ctors : &[u16],
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (DeclarsPtr<'l>, Step<MkIndTypesZst>) {
        match (rem_ind_names.read(ctx), rem_ind_types.read(ctx), rem_nums_ctors)  {

            (Cons(i_n, i_ns), Cons(i_t, i_ts), [num, nums @ ..]) => {
                let ctor_names_curr = rem_ctor_names.take(*num as usize, ctx);
                let ctor_names_rest = rem_ctor_names.skip(*num as usize, ctx);

                let (declars_tl, h1)  = self.mk_ind_types(
                    i_ns,
                    i_ts,
                    ctor_names_rest,
                    nums,
                    ctx
                );

                let declars_hd = <DeclarPtr>::new_inductive(
                    i_n,
                    self.uparams,
                    i_t,
                    self.num_params,
                    self.ind_names,
                    ctor_names_curr,
                    self.is_unsafe,
                    ctx
                );

                let declars = Cons(declars_hd, declars_tl).alloc(ctx);
                MkIndTypes::Step {
                    indblock : self.as_ptr(),
                    i_ns_hd : i_n,
                    i_ns_tl : i_ns,
                    i_ts_hd : i_t,
                    i_ts_tl : i_ts,
                    ctor_names_curr,
                    ctor_names_rest,
                    declars_tl,
                    ind_names : rem_ind_names,
                    ind_types : rem_ind_types,
                    ctor_names : rem_ctor_names,
                    declars_hd,
                    declars,
                    h1
                }.step(ctx)

            },
            _ => {
                let declars = Nil::<Declar>.alloc(ctx);
                MkIndTypes::Base {
                    indblock : self.as_ptr(),
                    ind_names : rem_ind_names,
                    ind_types : rem_ind_types, 
                    ctor_names : rem_ctor_names,
                    declars
                }.step(ctx)
            }
        }
    }

    
    pub fn declare_ind_types(
        mut self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (CheckedIndblock<'l>, DeclarsPtr<'l>) {
        let h1 = self.check_ind_types(ctx);

        let (_, h2) = self.is_zero();
        let (_, h3) = self.is_nonzero();
        
        let (ds, h4) = self.mk_ind_types(
            self.ind_names,
            self.ind_types,
            self.ctor_names,
            self.nums_ctors.as_slice(),
            ctx
        );

        let checked_indblock = self.as_checked(ctx);

        let step = AdmitDeclar::Inductives {
            env : ctx.last_admit(),
            indblock : checked_indblock.indblock_ptr,
            ds,
            params : checked_indblock.local_params,
            indices : checked_indblock.local_indices,
            ind_consts : checked_indblock.ind_consts,
            codom_level : checked_indblock.block_codom,
            is_zero : checked_indblock.is_zero.0,
            is_nonzero : checked_indblock.is_nonzero.0,
            checked_indblock : checked_indblock.as_ptr(),
            h1,
            h2,
            h3,
            h4
        }.step_only(ctx);
        ctx.admit_declars(ds, step);
        (checked_indblock, ds)
    }
}

impl<'l, 'e : 'l> CheckedIndblock<'l> {
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
        stripped_ctor_type : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<IsValidIndAppZst>) {
        let ((base_const, ctor_apps), h1) = stripped_ctor_type.unfold_apps(ctx);
        let b1 = (base_const == parent_ind_const);
        let ind_apps_len = ctor_apps.len(ctx);
        let (telescope_size, h2) = parent_ind_type.telescope_size(ctx);
        let b2 = (ind_apps_len == telescope_size as usize);

        if !(b1 && b2) {
            IsValidIndApp::BaseFf {
                checked_indblock : self.as_ptr(),
                ind_type : parent_ind_type,
                ind_const : parent_ind_const,
                unfolded_fun : base_const,
                stripped_ctor_type,
                ind_apps : ctor_apps,
                apps_len : ind_apps_len as u16,
                telescope_size,
                b1,
                b2,
                b : (b1 && b2),
                h1,
                h2,
            }.step(ctx)

        } else {
            let (b3, h3) = valid_param_apps(ctor_apps, self.local_params, ctx);
            IsValidIndApp::BaseTt {
                checked_indblock : self.as_ptr(),
                ind_type : parent_ind_type,
                ind_const : parent_ind_const,
                unfolded_fun : base_const,
                stripped_ctor_type,
                ind_apps : ctor_apps,
                apps_len : ind_apps_len as u16,
                telescope_size,
                b1,
                b2,
                b3,
                b : b1 && b2 && b3,
                h1,
                h2,
                h3,
            }.step(ctx)

        }
    }    


    pub fn which_valid_ind_app(
        &self,
        ind_types : ExprsPtr<'l>,
        ind_consts : ExprsPtr<'l>,
        u_i_ty : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (u16, Step<WhichValidIndAppZst>) {
        match (ind_types.read(ctx), ind_consts.read(ctx)) {
            (Cons(t, ts), Cons(c, cs)) => {
                let (is_valid_ind_app, h1) = self.is_valid_ind_app(t, c, u_i_ty, ctx);

                if is_valid_ind_app {
                    WhichValidIndApp::Base {
                        checked_indblock : self.as_ptr(),
                        u_i_ty,
                        ind_types_hd : t,
                        ind_types_tl : ts,
                        ind_consts_hd : c,
                        ind_consts_tl : cs,
                        ind_types,
                        ind_consts,
                        ind_ty_idx : 0u16,
                        h1
                    }.step(ctx)

                } else {
                    let (result, h2) = self.which_valid_ind_app(
                        ts, 
                        cs, 
                        u_i_ty, 
                        ctx
                    );

                    WhichValidIndApp::Step {
                        checked_indblock : self.as_ptr(),
                        u_i_ty,
                        ind_types_hd : t,
                        ind_types_tl : ts,
                        ind_consts_hd : c,
                        ind_consts_tl : cs,
                        ind_ty_idx_prime : result,
                        ind_types,
                        ind_consts,
                        ind_ty_idx : 1 + result,
                        h1,
                        h2,

                    }.step(ctx)
                }
            }
            _ => unreachable!("All applications must contain a valid use for SOME inductive datatype being declared")
        }
    }        

    /*
    This is executed against arguments to the constructor.
    */
    pub fn is_rec_argument(
        &self, 
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        ctor_arg : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<IsRecArgumentZst>) {
        let (ctor_arg_prime, h1) = ctor_arg.whnf(
            &mut ctx.as_tc(Some(self.uparams), None)
        );

        match ctor_arg_prime.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h2) = body.inst1(local, ctx);
                let (result, h3) = self.is_rec_argument(
                    ind_type,
                    ind_const, 
                    b_prime,
                    ctx
                );
                IsRecArgument::Step {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    serial : local.local_serial_infal(ctx),
                    ctor_arg_prime,
                    b_prime,
                    result,
                    ctor_arg,
                    local,
                    h1,
                    h2,
                    h3
                }.step(ctx)
            },
            _ => {
                let (result, h2) = self.is_valid_ind_app(
                    ind_type,
                    ind_const,
                    ctor_arg_prime, 
                    ctx
                );
                IsRecArgument::Base {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    ctor_arg,
                    ctor_arg_prime,
                    result,
                    h1,
                    h2,
                }.step(ctx)
            }
        }
    }        

    fn check_positivity1(
        &self,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        ctor_type : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Step<CheckPositivity1Zst> {
        if self.is_unsafe {
            CheckPositivity1::ByUnsafe {
                checked_indblock : self.as_ptr(),
                ind_type,
                ind_const,
                ctor_type
            }.step_only(ctx)
        } else {
            self.check_positivity1_aux(ind_type, ind_const, ctor_type, ctx)
        }

    }


    // This is only ONE of the binders/arguments from the constructor's telescope,
    // AFTER the block params have been removed. These are essentially
    // the "extra arguments" to the constructor.
    // When we match here on Pi { x, y }, `x` is the left hand side
    // of a function argument to an inductive constructor.
    // We need to search `y` to prevent non-positive occurrences like
    // | mk (f : A -> A -> thing A) : thing A
    fn check_positivity1_aux(
        &self,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        ctor_type : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Step<CheckPositivity1Zst> {
        let (ctor_type_prime, h1) = ctor_type.whnf(
            &mut ctx.as_tc(Some(self.uparams), None)
        );

        let short_result = ctor_type_prime.has_ind_occ(self.ind_names, ctx);

        match (short_result, ctor_type_prime.read(ctx)) {
            ((false, h2), _) => {
                CheckPositivity1::NoIndOccs {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    ctor_type,
                    ctor_type_prime,
                    h1,
                    h2,
                }.step_only(ctx)
            },
            ((true, _), Pi { b_name, b_type, b_style, body, .. }) => {
                let (binder_ind_occs, h2) = b_type.has_ind_occ(self.ind_names, ctx);
                assert!(!binder_ind_occs);

                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h3) = body.inst1(local, ctx);
                let h4 = self.check_positivity1_aux(ind_type, ind_const, b_prime, ctx);
                CheckPositivity1::Step {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    serial : local.local_serial_infal(ctx),
                    ctor_type,
                    b_prime,
                    ctor_type_prime,
                    local,
                    h1,
                    h2,
                    h3,
                    h4
                }.step_only(ctx)
            },
            ((true, _), _) => {
                let (is_valid, h2) = self.is_valid_ind_app(
                    ind_type, 
                    ind_const, 
                    ctor_type_prime,
                    ctx
                );
                assert!(is_valid);
                CheckPositivity1::BaseValid {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    ctor_type,
                    ctor_type_prime,
                    h1,
                    h2
                }.step_only(ctx)
            }
        }
    }    



    // This always begins with the full type/param list
    // #[params(block_uparams = "self.uparams")]
    pub fn check_ctor1(
        &self,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        ctor_type : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Step<CheckCtor1Zst> {
        match (ctor_type.read(ctx), rem_params.read(ctx)) {
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl)) => {

                let param_type = hd.local_type_infal(ctx);
                let h1 = b_type.assert_def_eq(param_type, &mut ctx.as_tc(Some(self.uparams), None));
                let (b_prime, h2) = body.inst1(hd, ctx);

                let h3 = self.check_ctor1(ind_type, ind_const, b_prime, tl, ctx);
                match hd.read(ctx) {
                    Local { b_name: p_n, b_type: p_t, b_style: p_s, serial } => {
                        CheckCtor1::StepParam {
                            checked_indblock : self.as_ptr(),
                            ind_type,
                            ind_const,
                            p_n,
                            p_t,
                            p_s,
                            serial,
                            params_tl : tl,
                            n : b_name,
                            t : b_type,
                            s : b_style,
                            b : body,
                            b_prime,
                            ps_hd : hd,
                            ps : rem_params,
                            ctor_type,
                            h1,
                            h2,
                            h3,
                        }.step_only(ctx)
                    }
                    _ => unreachable!("non-local in check_ctor1 params branch")
                }
            },
            (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
                let h1 = self.check_positivity1(ind_type, ind_const, b_type, ctx);


                // assertion that b_type is a well formed inhabitant of some sort.
                let (sort_level, h2) = b_type.ensure_type(
                    &mut ctx.as_tc(Some(self.uparams), None)
                );

                if let (true, h3) = self.is_zero {
                    let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                    let (b_prime, h4) = body.inst1(local, ctx);
                    let h5 = self.check_ctor1(ind_type, ind_const, b_prime, rem_params, ctx);
                    CheckCtor1::StepProp {
                        checked_indblock : self.as_ptr(),
                        ind_type,
                        ind_const,
                        n : b_name,
                        t : b_type,
                        s : b_style,
                        b : body,
                        sort_level,
                        serial : local.local_serial_infal(ctx),
                        b_prime,
                        rem_params,
                        ctor_type,
                        local_expr : local,
                        h1,
                        h2,
                        h3,
                        h4,
                        h5
                    }.step_only(ctx)
                } else if let (true, h3) = sort_level.leq(self.block_codom, ctx) {
                    let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                    let (b_prime, h4) = body.inst1(local, ctx);
                    let h5 = self.check_ctor1(ind_type, ind_const, b_prime, rem_params, ctx);
                    CheckCtor1::StepLe {
                        checked_indblock : self.as_ptr(),
                        ind_type,
                        ind_const,
                        n : b_name,
                        t : b_type,
                        s : b_style,
                        b : body,
                        sort_level,
                        serial : local.local_serial_infal(ctx),
                        b_prime,
                        rem_params,
                        ctor_type,
                        local_expr : local,
                        h1,
                        h2,
                        h3,
                        h4,
                        h5
                    }.step_only(ctx)
                } else {
                    panic!(
                        "Constructor argument was too large for \
                        the corresponding inductive type!\n
                        constructor was : {}\n overall was : {}\n", 
                        sort_level.nanoda_dbg(ctx), 
                        self.block_codom.nanoda_dbg(ctx))
                }
            },
            _ => {
                let (b, h1) = self.is_valid_ind_app(ind_type, ind_const, ctor_type, ctx);
                assert!(b);
                CheckCtor1::Base {
                    checked_indblock : self.as_ptr(),
                    ind_type,
                    ind_const,
                    ctor_type,
                    rem_params,
                    h1
                }.step_only(ctx)
            }
        }
    }    

    // The list is passed L -> R, IE [base, step1, step2]
    //  where a `group` means the list of constructors for one inductive
    // type in a block, as opposed to all of the constructors in a block, which may 
    // be spread across a number of mutually inductive types.   
    pub fn mk_ctors_group(
        &self,
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_ctor_names : NamesPtr<'l>,
        rem_ctor_types : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (DeclarsPtr<'l>, Step<MkCtorGroup1Zst>) {
        match (rem_ctor_names.read(ctx), rem_ctor_types.read(ctx)) {
            (Cons(n, ns), Cons(t, ts)) => {
                // recurse first
                let (ds_tl, h1) = self.mk_ctors_group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    ns, 
                    ts, 
                    ctx
                );

                let (telescope_size, h2) = t.telescope_size(ctx);
                let num_fields = telescope_size - self.num_params;

                // assertion.
                let h3 = self.check_ctor1(ind_type, ind_const, t, self.local_params, ctx);

                let d = <DeclarPtr>::new_ctor(
                    n, 
                    self.uparams, 
                    t, 
                    ind_name, 
                    num_fields,
                    self.num_params, 
                    self.is_unsafe, 
                    ctx
                );

                let ds = Cons(d, ds_tl).alloc(ctx);

                MkCtorGroup1::Step {
                    checked_indblock : self.as_ptr(),
                    ind_name,
                    ind_type,
                    ind_const,
                    //
                    ns_hd : n,
                    ns_tl : ns,
                    ts_hd : t,
                    ts_tl : ts,
                    telescope_size,
                    ds_tl,
                    num_fields,
                    d,
                    rem_ctor_names,
                    rem_ctor_types,
                    ds,
                    h1,
                    h2,
                    h3
                }.step(ctx)

            },
            (Nil, Nil) => {
                let ds = Nil::<Declar>.alloc(ctx);
                MkCtorGroup1::Base {
                    checked_indblock : self.as_ptr(),
                    ind_name,
                    ind_type,
                    ind_const,
                    rem_ctor_names,
                    rem_ctor_types,
                    ds
                }.step(ctx)
            }
            _ => unreachable!("unequal lengths @ declare_ctors_group!")
        }
    }

    pub fn mk_ctors(
        &self,
        rem_ind_ns : NamesPtr<'l>,
        rem_ind_ts : ExprsPtr<'l>,
        rem_ind_cs : ExprsPtr<'l>,
        nums_cs : &[u16],
        rem_ctor_ns : NamesPtr<'l>,
        rem_ctor_ts : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (DeclarsPtr<'l>, Step<MkCtorsZst>) {
        match (rem_ind_ns.read(ctx), rem_ind_ts.read(ctx), rem_ind_cs.read(ctx), nums_cs) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [num, nums @ ..]) => {
                let cn_hd = rem_ctor_ns.take(*num as usize, ctx);
                let cn_tl = rem_ctor_ns.skip(*num as usize, ctx);

                let ct_hd = rem_ctor_ts.take(*num as usize, ctx);
                let ct_tl = rem_ctor_ts.skip(*num as usize, ctx);
                let (rest_ds, h1) = self.mk_ctors(i_ns, i_ts, i_cs, nums, cn_tl, ct_tl, ctx);
                let (curr_ds, h2) = self.mk_ctors_group(i_n, i_t, i_c, cn_hd, ct_hd, ctx);
                let ds = curr_ds.concat(rest_ds, ctx);
                MkCtors::Step {
                    checked_indblock : self.as_ptr(),
                    ind_n_hd : i_n,
                    ind_n_tl : i_ns,
                    ind_t_hd : i_t,
                    ind_t_tl : i_ts,
                    ind_c_hd : i_c,
                    ind_c_tl : i_cs,
                    curr_c_ns : cn_hd,
                    rest_c_ns : cn_tl,
                    curr_c_ts : ct_hd,
                    rest_c_ts : ct_tl,
                    curr_ds,
                    rest_ds,
                    rem_ind_names : rem_ind_ns,
                    rem_ind_types : rem_ind_ts,
                    rem_ind_consts : rem_ind_cs,
                    rem_c_names : rem_ctor_ns,
                    rem_c_types : rem_ctor_ts,
                    ds,
                    h1,
                    h2,
                }.step(ctx)
            },    
            (Nil, Nil, Nil, []) => {
                let result = Nil::<Declar>.alloc(ctx);
                MkCtors::Base {
                    checked_indblock : self.as_ptr(),
                    rem_ind_names : rem_ind_ns,
                    rem_ind_types : rem_ind_ts,
                    rem_ind_consts : rem_ind_cs,
                    rem_c_names : rem_ctor_ns,
                    rem_c_types : rem_ctor_ts,
                    ds : result,
                }.step(ctx)

            }
            _ => unreachable!("Mismatch in lengths; inductive::mk_ctors")
        }
    }

    pub fn declare_ctors(&self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let (ds, h1) = self.mk_ctors(
            self.ind_names, 
            self.ind_types, 
            self.ind_consts,
            self.nums_ctors.as_slice(),
            self.ctor_names,
            self.ctor_types,
            ctx
        );

        let step = AdmitDeclar::Constructors {
            env : ctx.last_admit(),
            indblock : self.as_ptr(),
            ctors : ds,
            h1
        }.step_only(ctx);
        ctx.admit_declars(ds, step);
    }    

    /*
    The pi binder types we collect after passing the parameters
    are NOT indices, they're just constructor arguments.
    We know what the indices are, because they're the first 0 or more
    argumeents to the unfolded expression at the end.
    */
    #[allow(unconditional_recursion)]
    pub fn large_elim_test_aux(
        &self, 
        ctor_type_cursor : ExprPtr<'l>,
        params_rem : u16,
        nonzero_ctor_args : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<LargeElimTestAuxZst>) {
        match ctor_type_cursor.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } if params_rem != 0 => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h1) = body.inst1(local, ctx);
                let params_rem_prime = params_rem - 1;
                let (large_eliminating, h2) = self.large_elim_test_aux(
                    b_prime, 
                    params_rem_prime, 
                    nonzero_ctor_args, 
                    ctx
                );
                LargeElimTestAux::StepParam {
                    params_rem,
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    serial : local.local_serial_infal(ctx),
                    b_prime,
                    large_eliminating,
                    params_rem_prime,
                    ctor_type : ctor_type_cursor,
                    local_expr : local,
                    nonzero_ctor_args,
                    h1,
                    h2,
                }.step(ctx)
            },
            // We're assembling a list of the binders that are known to NOT
            // be props/in Sort 0
            Pi { b_name, b_type, b_style, body, .. } => {
                assert_eq!(params_rem, 0);
                let (t_level, h1) = b_type.ensure_type(&mut ctx.as_tc(Some(self.uparams), None));
                let (b_type_is_zero, h2) = t_level.is_zero(ctx);

                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h3) = body.inst1(local, ctx);

                match b_type_is_zero {
                    // If the binder type is in Sort 0, just pass over it.
                    true => {
                        let (large_eliminating, h4) = self.large_elim_test_aux(
                            b_prime, 
                            params_rem, 
                            nonzero_ctor_args,
                            ctx
                        );

                        LargeElimTestAux::StepZero {
                            n : b_name,
                            t : b_type,
                            s : b_style,
                            b : body,
                            t_level,
                            serial : local.local_serial_infal(ctx),
                            b_prime,
                            nonzero_ctor_args,
                            large_eliminating,
                            params_rem,
                            ctor_type : ctor_type_cursor,
                            local_expr : local,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step(ctx)
                    }
                    // If the binder type is NOT in sort 0, add it to the list
                    // of constructor args that need to be checked
                    false => {
                        let (large_eliminating, h4) = self.large_elim_test_aux(
                            b_prime,
                            params_rem,
                            Cons(local, nonzero_ctor_args).alloc(ctx),
                            ctx
                        );

                        LargeElimTestAux::StepNonzero {
                            n : b_name,
                            t : b_type,
                            s : b_style,
                            b : body,
                            t_level,
                            serial : local.local_serial_infal(ctx),
                            b_prime,
                            nonzero_ctor_args,
                            large_eliminating,
                            params_rem,
                            ctor_type : ctor_type_cursor,
                            local_expr : local,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step(ctx)                       
                    }
                }
            },
            _ => {
                assert_eq!(params_rem, 0);
                // In this context, args (the exprs being applied to the ind_const)
                // is the inductive block's params + the base type's indices
                let (b, h1) = ctor_type_cursor.is_pi(ctx);
                assert!(!b);
                let ((ctor_fun, ctor_args), h2) = ctor_type_cursor.unfold_apps(ctx);
                // if the list of non-prop constructor args is NOT a subset of
                // the exprs being applied to the inductive (which is params + indices)
                // then we can say that this type ONLY eliminates into Prop/Sort 0
                let (large_eliminating, h3) = nonzero_ctor_args.subset(ctor_args, ctx);

                LargeElimTestAux::Base {
                    ctor_type : ctor_type_cursor,
                    ctor_fun,
                    ctor_args,
                    nonzero_ctor_args,
                    large_eliminating,
                    params_rem,
                    h1,
                    h2,
                    h3
                }.step(ctx)

            }
        }
    }

    // FIXME Control flow needs to be broken up here too.
    pub fn large_elim_test(
        &self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<LargeElimTestZst>) {
        let (is_nonzero, h1) = self.is_nonzero;

        // If we're dealing with an inductive type, then tt
        if is_nonzero {
            return LargeElimTest::Nonzero {
                checked_indblock : self.as_ptr(),
                large_eliminating : true,
                h1
            }.step(ctx)
        } 

        // if we have a mutual that's not a type, then ff
        let len = self.ind_types.len(ctx);
        if len > 1 {
            return LargeElimTest::IsMutual {
                checked_indblock : self.as_ptr(),
                large_eliminating : false,
                h1,
            }.step(ctx)
        }

        let ctors_len = self.ctor_types.len(ctx);

        // if not a type, and more than one constructor, then ff
        if ctors_len > 1 {
            return LargeElimTest::ManyCtors {
                checked_indblock : self.as_ptr(),
                large_eliminating : false,
                h1,
            }.step(ctx)
        }


        match self.ctor_types.get(0, ctx) {
            // if no constructors (ie false) then tt
            None => {
                LargeElimTest::NoCtors {
                    checked_indblock : self.as_ptr(),
                    large_eliminating : true,
                }.step(ctx)
            },
            // if exactly 1 constructor, then let `large_elim_test_aux` decide.
            Some(only_ctor) => {
                let (large_eliminating, h2) = self.large_elim_test_aux(
                    only_ctor,
                    self.num_params,
                    Nil::<Expr>.alloc(ctx),
                    ctx
                );

                LargeElimTest::ByAux {
                    checked_indblock : self.as_ptr(),
                    ctor_type : only_ctor,
                    large_eliminating,
                    h1,
                    h2
                }.step(ctx)
            }
        }
    }    

    pub fn gen_elim_level(&self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) -> LevelPtr<'l> {
        let mut i = 0u64;
        let base = name!("u", ctx);
        let mut p = base.new_param(ctx);

        while let Some(..) = p.pos(self.uparams, ctx).0 {
            i += 1;
            p = base.new_num(i, ctx).new_param(ctx);
        }
        p
    }    

    pub fn mk_elim_level(
        &mut self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (LevelPtr<'l>, Step<MkElimLevelZst>) { 
        let (elim_level, step) = match self.large_elim_test(ctx) {
            (true, h1) => {
                let elim_level = self.gen_elim_level(ctx);
                let (b, h2) = elim_level.pos(self.uparams, ctx);
                assert!(b.is_none());
                MkElimLevel::Large {
                    checked_indblock : self.as_ptr(),
                    elim_level,
                    h1,
                    h2,
                }.step(ctx)
            },
            (false, h1) => {
                let elim_level = Level::Zero.alloc(ctx);
                MkElimLevel::Small {
                    checked_indblock : self.as_ptr(),
                    elim_level,
                    h1,
                }.step(ctx)
            }
        };

        self.elim_level = Some((elim_level, step));

        (elim_level, step)

    }    

    
    pub fn init_k_target_aux(
        &self, 
        ctor_cursor : ExprPtr<'l>, 
        params_rem : u16, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<InitKTargetAuxZst>) {
        match ctor_cursor.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } if params_rem != 0 => {
                let params_rem_prime = params_rem - 1;
                let (k_target, h1) = self.init_k_target_aux(body, params_rem_prime, ctx);
                InitKTargetAux::Step {
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    params_rem,
                    k_target,
                    ctor_type : ctor_cursor,
                    params_rem_prime,
                    h1
                }.step(ctx)
            }
            Pi {..} => {
                let (is_pi, h1) = ctor_cursor.is_pi(ctx);
                assert!(is_pi);
                assert_eq!(params_rem, 0);
                let k_target = false;
                InitKTargetAux::Base {
                    ctor_type : ctor_cursor,
                    is_pi,
                    params_rem,
                    k_target,
                    h1
                }.step(ctx)
            }
            _ => {
                let (is_pi, h1) = ctor_cursor.is_pi(ctx);
                assert!(!is_pi);
                assert_eq!(params_rem, 0);
                let k_target = true;
                InitKTargetAux::Base {
                    ctor_type : ctor_cursor,
                    is_pi,
                    params_rem,
                    k_target,
                    h1
                }.step(ctx)
            }
        }
    }    

    pub fn init_k_target(
        &mut self,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (bool, Step<InitKTargetZst>) {
        let mut clos = || {
            let ind_types_len = self.ind_types.len(ctx);
            if ind_types_len > 1 {
                return InitKTarget::IsMutual {
                    checked_indblock : self.as_ptr(),
                    k_target : false,
                }.step(ctx)
            }

            let (is_zero, h1) = self.is_zero;
            if !is_zero {
                return InitKTarget::Nonzero {
                    checked_indblock : self.as_ptr(),
                    k_target : false,
                    h1
                }.step(ctx)
            }

            let ctors_len = self.ctor_types.len(ctx);
            if !(ctors_len == 1) {
                return InitKTarget::NotOneCtor {
                    checked_indblock : self.as_ptr(),
                    k_target : false,
                }.step(ctx)
            }
            
            let only_ctor = self.ctor_types.get(0, ctx).expect(
                "Failed to get checked `0` elem in init_k_target"
            );

            let (k_target, h1) = self.init_k_target_aux(only_ctor, self.num_params, ctx);

            InitKTarget::ByAux {
                checked_indblock : self.as_ptr(),
                ctor_type : only_ctor,
                k_target,
                h1
            }.step(ctx)           

        };

        let (k_target, step) = clos();

        
        self.k_target = Some(k_target);
        (k_target, step)
    }

    // These are 1 for 1 with the inductive types list;
    // also goes [A, B, C]
    // for types [A, B, C]
    pub fn mk_majors_aux(
        &self, 
        nums_indices : &[u16],
        ind_consts : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<MkMajorsAuxZst>) {
        match (nums_indices, ind_consts.read(ctx)) {
            ([num, nums @ ..], Cons(ic, ics)) => {
                let indices_l = local_indices.take(*num as usize, ctx);
                let indices_r = local_indices.skip(*num as usize, ctx);

                let (majors_tl, h1) = self.mk_majors_aux(nums, ics, indices_r, ctx);

                // mk_major1
                let major_name = name!("t", ctx);
                let (major_typeA, h2) = ic.foldl_apps(self.local_params, ctx);
                let (major_typeB, h3) = major_typeA.foldl_apps(indices_l, ctx);
                let major = <ExprPtr>::new_local(major_name, major_typeB, Default, ctx);
                //

                let majors = Cons(major, majors_tl).alloc(ctx);
                MkMajorsAux::Step {
                    checked_indblock : self.as_ptr(),
                    indices_l,
                    indices_r,
                    ind_consts_hd : ic,
                    ind_consts_tl : ics,
                    majors_tl,
                    major_typeA,
                    major_typeB,
                    serial : major.local_serial_infal(ctx),
                    indices : local_indices,
                    ind_consts,
                    major_name,
                    major_bstyle : Default,
                    majors_hd : major,
                    majors,
                    h1,
                    h2,
                    h3
                }.step(ctx)
            },
            ([], Nil) => {
                let majors = Nil::<Expr>.alloc(ctx);
                MkMajorsAux::Base {
                    checked_indblock : self.as_ptr(),
                    indices : local_indices,
                    ind_consts,
                    majors
                }.step(ctx)
            }
            _ => unreachable!("Uneven lengths in mk_majors")
        }
    }        

    pub fn mk_majors(&mut self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) -> Step<MkMajorsAuxZst> { 
        let (majors, h1) = self.mk_majors_aux(
            self.nums_indices.as_slice(),
            self.ind_consts, 
            self.local_indices, 
            ctx
        );
        self.majors = Some(majors);
        h1
    }

    pub fn mk_motive(
        &self,
        local_indices : ExprsPtr<'l>,
        major : ExprPtr<'l>,
        ind_type_idx : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprPtr<'l>, Step<MkMotiveZst>) {

        match self.use_dep_elim() {
            false => {
                let elim_sort = self.elim_level().0.new_sort(ctx);
                let (motive_type, h1) = local_indices.fold_pis(elim_sort, ctx);
                let motive_name = name!("C", ctx).new_num(ind_type_idx as u64, ctx);

                let motive = <ExprPtr>::new_local(motive_name, motive_type, Implicit, ctx);

                MkMotive::Indep {
                    elim_level : self.elim_level().0,
                    indices : local_indices,
                    ind_type_idx,
                    major,
                    serial : motive.local_serial_infal(ctx),
                    motive_type,
                    elim_sort, 
                    motive_name,
                    motive_bstyle : Implicit,
                    motive,
                    h1
                }.step(ctx)               

            },
            true => {
                let elim_sort = self.elim_level().0.new_sort(ctx);
                let (motive_typeA, h1) = major.apply_pi(elim_sort, ctx);
                let (motive_typeB, h2) = local_indices.fold_pis(motive_typeA, ctx);
                let motive_name = name!("C", ctx).new_num(ind_type_idx as u64, ctx);

                let motive = <ExprPtr>::new_local(motive_name, motive_typeB, Implicit, ctx);
                MkMotive::Dep {
                    elim_level : self.elim_level().0,
                    indices : local_indices,
                    ind_type_idx,
                    major,
                    serial : motive.local_serial_infal(ctx),
                    motive_typeA,
                    motive_typeB,
                    elim_sort,
                    motive_name,
                    motive_bstyle : Implicit,
                    motive,
                    h1,
                    h2
                }.step(ctx)               

            }
        }
    }



    // Motives (C) are 1 for 1 with ind types being declared. Also go L -> R.
    // Are numbered as IE [C.1, C.2, C.3]
    // for a list of inds [A, B, C]
    pub fn mk_motives_aux(
        &self, 
        nums_indices : &[u16],
        majors : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        ind_type_idx : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<MkMotivesZst>) {
        match (nums_indices, majors.read(ctx)) {
            ([num, nums @ ..], Cons(mj, mjs)) => {
                let indices_l = local_indices.take(*num as usize, ctx);
                let indices_r = local_indices.skip(*num as usize, ctx);

                let (motives_tl, h1) = self.mk_motives_aux(nums, mjs, indices_r, ind_type_idx + 1, ctx);
                let (motives_hd, h2) = self.mk_motive(indices_l, mj, ind_type_idx, ctx);
                let motives = Cons(motives_hd, motives_tl).alloc(ctx);
                MkMotives::Step {
                    elim_level : self.elim_level().0,
                    ind_type_idx,
                    majors_hd : mj,
                    majors_tl : mjs,
                    indices_l,
                    indices_r,
                    motives_hd,
                    motives_tl,
                    ind_type_idx_prime : ind_type_idx + 1,
                    majors,
                    indices : local_indices,
                    motives,
                    h1,
                    h2,
                }.step(ctx)
            },
            ([], Nil) => {
                let motives = Nil::<Expr>.alloc(ctx);
                MkMotives::Base {
                    elim_level : self.elim_level().0,
                    ind_type_idx,
                    majors,
                    indices : local_indices,
                    motives
                }.step(ctx)

            }
            _ => unreachable!("Uneven list lengths in mk_motives")
        }
    }        

    
    pub fn mk_motives(&mut self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) -> Step<MkMotivesZst> {
        let (motives, h1) = self.mk_motives_aux(
            self.nums_indices.as_slice(),
            self.majors(), 
            self.local_indices, 
            0u16, 
            ctx
        );
        self.motives = Some(motives);
        h1
    }

    // The main thing this does is make two lists, the one 
    // on the left is all of the constructor's arguments, 
    // and the one on the right is only the constructors 
    // arguments that are recursive.
    pub fn sep_rec_ctor_args(
        &self, 
        ind_t : ExprPtr<'l>,
        ind_c : ExprPtr<'l>,
        ctor_type_cursor : ExprPtr<'l>,
        rem_params : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ((ExprsPtr<'l>, ExprsPtr<'l>, ExprPtr<'l>), Step<SepRecCtorArgsZst>) {
        match (ctor_type_cursor.read(ctx), rem_params.read(ctx)) {
            (Pi { b_name, b_type, b_style, body, .. }, Cons(hd, tl)) => {
                let (b_prime, h1) = body.inst1(hd, ctx);
                let (result, h2) = self.sep_rec_ctor_args(
                    ind_t, 
                    ind_c, 
                    b_prime, 
                    tl, 
                    ctx
                );
                SepRecCtorArgs::Param {
                    checked_indblock : self.as_ptr(),
                    ind_type : ind_t,
                    ind_const : ind_c,
                    inner_type : result.2,
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    b_prime,
                    all_args : result.0,
                    rec_args : result.1,
                    rem_params_hd : hd,
                    rem_params_tl : tl,
                    rem_params,
                    ctor_type : ctor_type_cursor,
                    result,
                    h1,
                    h2
                }.step(ctx)
            },
            (Pi { b_name, b_type, b_style, body, .. }, Nil) => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h1) = body.inst1(local, ctx);

                let ((all_args_tl, rec_args_tl, inner), h2) = self.sep_rec_ctor_args(
                    ind_t, 
                    ind_c, 
                    b_prime, 
                    rem_params, 
                    ctx
                );

                let all_args = Cons(local, all_args_tl).alloc(ctx);
                let (is_rec, h3) = self.is_rec_argument(ind_t, ind_c, b_type, ctx);
                match is_rec {
                    false => {
                        let rec_args = rec_args_tl;
                        let result = (all_args, rec_args, inner);
                        SepRecCtorArgs::NonrecArg {
                            checked_indblock : self.as_ptr(),
                            ind_type : ind_t,
                            ind_const : ind_c,
                            inner_type : inner,
                            n : b_name,
                            t : b_type,
                            s : b_style,
                            b : body,
                            serial : local.local_serial_infal(ctx),
                            b_prime,
                            all_args_tl,
                            rec_args,
                            rem_params,
                            ctor_type : ctor_type_cursor,
                            arg : local,
                            all_args,
                            result,
                            h1,
                            h2,
                            h3,
                        }.step(ctx)

                    },
                    true => {
                        let rec_args = Cons(local, rec_args_tl).alloc(ctx);
                        let result = (all_args, rec_args, inner);
                        SepRecCtorArgs::RecArg {
                            checked_indblock : self.as_ptr(),
                            ind_type : ind_t,
                            ind_const : ind_c,
                            inner_type : inner,
                            n : b_name,
                            t : b_type,
                            s : b_style,
                            b : body,
                            serial : local.local_serial_infal(ctx),
                            b_prime,
                            all_args_tl,
                            rec_args_tl,
                            rem_params,
                            ctor_type : ctor_type_cursor,
                            arg : local,
                            all_args,
                            rec_args,
                            result,
                            h1,
                            h2,
                            h3,
                        }.step(ctx)
                    }
                }
            },
            _ => {
                let all_args= Nil::<Expr>.alloc(ctx);
                let rec_args = Nil::<Expr>.alloc(ctx);
                let result = (all_args, rec_args, ctor_type_cursor);
                SepRecCtorArgs::Base {
                    checked_indblock : self.as_ptr(),
                    ind_type : ind_t,
                    ind_const : ind_c,
                    rem_params,
                    ctor_type : ctor_type_cursor,
                    all_args,
                    rec_args,
                    inner_type : ctor_type_cursor,
                    result
                }.step(ctx)
            }
        }
    }       

    pub fn get_i_indices(
        &self, 
        type_cursor : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ((u16, ExprsPtr<'l>), Step<GetIIndicesZst>) {
        // Position in self.ind_types of the inductive type being applied/created
        // by the constructor
        let (valid_app_idx, h1) = self.which_valid_ind_app(
            self.ind_types,
            self.ind_consts,
            type_cursor,
            ctx
        );

        let ((fun, args), h2) = type_cursor.unfold_apps(ctx);
        let indices = args.skip(self.num_params as usize, ctx);
        let result = (valid_app_idx, indices);
        GetIIndices::Base {
            checked_indblock : self.as_ptr(),
            type_cursor,
            type_fun : fun,
            type_args : args,
            valid_app_idx,
            indices,
            result,
            h1,
            h2
        }.step(ctx)
    }    

    // used by mk_minors and mk_rec_rules
    #[allow(unconditional_recursion)]
    pub fn handle_rec_args_aux(
        &self,
        rec_arg_cursor : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> ((ExprPtr<'l>, ExprsPtr<'l>), Step<HandleRecArgsAuxZst>) {
        match rec_arg_cursor.read(ctx) {
            Pi { b_name, b_type, b_style, body, .. } => {
                let local = <ExprPtr>::new_local(b_name, b_type, b_style, ctx);
                let (b_prime, h1) = body.inst1(local, ctx);
                let (b_prime_red, h2) = b_prime.whnf(&mut ctx.as_tc(Some(self.uparams), None));
                let ((inner, args_tl), h3) = self.handle_rec_args_aux(b_prime_red, ctx);
                let args = Cons(local, args_tl).alloc(ctx);
                let result = (inner, args);
                HandleRecArgsAux::Step {
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    serial : local.local_serial_infal(ctx),
                    b_prime,
                    b_prime_red,
                    inner,
                    args_tl,
                    type_cursor : rec_arg_cursor,
                    local_expr : local,
                    args,
                    result,
                    h1,
                    h2,
                    h3
                }.step(ctx)
            },
            _ => {
                let result = (rec_arg_cursor, Nil::<Expr>.alloc(ctx));
                HandleRecArgsAux::Base {
                    type_cursor : result.0,
                    args : result.1,
                    result
                }.step(ctx)
            }
        }
    }    
    
    pub fn handle_rec_args_minor(
        &self,
        rem_rec_args : ExprsPtr<'l>,
        self_idx : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<HandleRecArgsMinorZst>) {
        match rem_rec_args.read(ctx) {
            Cons(hd, tl) => {
                let self_idx_prime = self_idx + 1;
                let (result_tl, h1) = self.handle_rec_args_minor(tl, self_idx_prime, ctx);

                let (u_i_ty, h2) = hd.infer(InferOnly, &mut ctx.as_tc(None, None));
                let (u_i_ty_red, h3) = u_i_ty.whnf(&mut ctx.as_tc(Some(self.uparams), None));

                let ((inner , rec_aux_result), h4) = self.handle_rec_args_aux(u_i_ty_red, ctx);

                let ((valid_pos, indices_result), h5) = self.get_i_indices(inner, ctx);
                
                let motive = match self.motives().get(valid_pos as usize, ctx) {
                    Some(motive) => motive,
                    None => panic!("Failed to get specified motive")
                };

                let (motive_appA, h6) = motive.foldl_apps(indices_result, ctx);

                let v_name = name!("v", ctx).new_num(self_idx as u64, ctx);
                
                match self.use_dep_elim() {
                    false => {
                        let (v_i_ty, h7) = rec_aux_result.fold_pis(motive_appA, ctx);
                        let result_hd = <ExprPtr>::new_local(v_name, v_i_ty, Default, ctx);
                        let result = Cons(result_hd, result_tl).alloc(ctx);
                        HandleRecArgsMinor::StepIndep {
                            checked_indblock : self.as_ptr(),
                            motives : self.motives(),
                            self_idx,
                            rec_args_hd : hd,
                            rec_args_tl : tl,
                            result_tl,
                            u_i_ty,
                            u_i_ty_red,
                            inner,
                            rec_aux_result,
                            indices_result,
                            motive,
                            valid_pos,
                            motive_appA,
                            v_i_ty,
                            serial : result_hd.local_serial_infal(ctx),
                            rec_args : rem_rec_args,
                            self_idx_prime,
                            v_name,
                            result_hd,
                            result,
                            h1,
                            h2,
                            h3,
                            h4,
                            h5,
                            h6,
                            h7
                        }.step(ctx)
                    }
                    true => {
                        let (u_app, h7) = hd.foldl_apps(rec_aux_result, ctx);
                        let motive_appB = motive_appA.new_app(u_app, ctx);
                        let (v_i_ty, h8) = rec_aux_result.fold_pis(motive_appB, ctx);
                        let result_hd = <ExprPtr>::new_local(v_name, v_i_ty, Default, ctx);
                        let result = Cons(result_hd, result_tl).alloc(ctx);
                        HandleRecArgsMinor::StepDep {
                            checked_indblock : self.as_ptr(),
                            motives : self.motives(),
                            self_idx,
                            rec_args_hd : hd,
                            rec_args_tl : tl,
                            result_tl,
                            u_i_ty,
                            u_i_ty_red,
                            inner,
                            rec_aux_result,
                            indices_result,
                            motive,
                            valid_pos,
                            motive_appA,
                            v_i_ty,
                            serial : result_hd.local_serial_infal(ctx),
                            u_app,
                            rec_args : rem_rec_args,
                            self_idx_prime,
                            v_name,
                            result_hd,
                            motive_appB,
                            result,
                            h1,
                            h2,
                            h3,
                            h4,
                            h5,
                            h6,
                            h7,
                            h8
                        }.step(ctx)                       
                    }
                }
            },
            Nil => {
                let result = rem_rec_args;
                HandleRecArgsMinor::Base {
                    checked_indblock : self.as_ptr(),
                    rem_rec_args,
                    result,
                }.step(ctx)

            }
        }

    }

    pub fn mk_minors_group(
        &self, 
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_ctor_names : NamesPtr<'l>,
        rem_ctor_types : ExprsPtr<'l>,
        ctor_idx : u16,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<MkMinorsGroupZst>) {
        match (rem_ctor_names.read(ctx), rem_ctor_types.read(ctx)) {
            (Cons(c_n, c_ns), Cons(c_t, c_ts)) => {
                let (minors_tl, h1) = self.mk_minors_group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    c_ns, 
                    c_ts, 
                    ctor_idx + 1, 
                    ctx
                );

                let ((all_args, rec_args, inner), h2) =
                    self.sep_rec_ctor_args(
                        ind_type,
                        ind_const,
                        c_t,
                        self.local_params,
                        ctx
                );

                let ((valid_pos, indices), h3) = self.get_i_indices(inner, ctx);
                
                let motive = match self.motives().get(valid_pos as usize, ctx) {
                    Some(motive) => motive,
                    None => panic!("Failed to get specified motive")
                };

                let (c_appA, h4) = motive.foldl_apps(indices, ctx);

                let minor_name = name!("m", ctx).new_num(ctor_idx as u64, ctx);
                match self.use_dep_elim() {
                    false => {
                        let (v, h5) = self.handle_rec_args_minor(rec_args, 0, ctx);

                        let (minor_typeA, h6) = v.fold_pis(c_appA, ctx);
                        let (minor_typeB, h7) = all_args.fold_pis(minor_typeA, ctx);
                        let minor = <ExprPtr>::new_local(minor_name, minor_typeB, Default, ctx);

                        let minors = Cons(minor, minors_tl).alloc(ctx);

                        MkMinorsGroup::StepIndep {
                            checked_indblock : self.as_ptr(),
                            motives : self.motives(),
                            ind_name,
                            ind_type,
                            ind_const,
                            ctor_idx,
                            ctor_names_hd : c_n,
                            ctor_names_tl : c_ns,
                            ctor_types_hd : c_t,
                            ctor_types_tl : c_ts,
                            minors_tl,
                            all_args,
                            rec_args,
                            inner,
                            indices,
                            valid_pos,
                            motive,
                            c_appA,
                            v,
                            minor_typeA,
                            minor_typeB,
                            minor_serial : minor.local_serial_infal(ctx),
                            ctor_idx_prime : ctor_idx + 1,
                            rem_ctor_names,
                            rem_ctor_types,
                            minor_name,
                            minor,
                            minors,
                            h1,
                            h2,
                            h3,
                            h4,
                            h5,
                            h6,
                            h7
                        }.step(ctx)


                    },
                    true => {
                        let rhsA = <ExprPtr>::new_const(c_n, self.uparams, ctx);
                        let (rhsB, h5) = rhsA.foldl_apps(self.local_params, ctx);
                        let (rhsC, h6) = rhsB.foldl_apps(all_args, ctx);
                        let c_appB = c_appA.new_app(rhsC, ctx);

                        let (v, h7) = self.handle_rec_args_minor(rec_args, 0, ctx);

                        let (minor_typeA, h8) = v.fold_pis(c_appB, ctx);
                        let (minor_typeB, h9) = all_args.fold_pis(minor_typeA, ctx);
                        let minor = <ExprPtr>::new_local(minor_name, minor_typeB, Default, ctx);

                        let minors = Cons(minor, minors_tl).alloc(ctx);

                        MkMinorsGroup::StepDep {
                            checked_indblock : self.as_ptr(),
                            motives : self.motives(),
                            ind_name,
                            ind_type,
                            ind_const,
                            ctor_idx,
                            ctor_names_hd : c_n,
                            ctor_names_tl : c_ns,
                            ctor_types_hd : c_t,
                            ctor_types_tl : c_ts,
                            minors_tl,
                            all_args,
                            rec_args,
                            inner,
                            indices,
                            valid_pos,
                            motive,
                            c_appA,
                            v,
                            minor_typeA,
                            minor_typeB,
                            minor_serial : minor.local_serial_infal(ctx),
                            rhsB,
                            rhsC,
                            ctor_idx_prime : ctor_idx + 1,
                            rem_ctor_names,
                            rem_ctor_types,
                            rhsA,
                            c_appB,
                            minor_name,
                            minor,
                            minors,
                            h1,
                            h2,
                            h3,
                            h4,
                            h5,
                            h6,
                            h7,
                            h8,
                            h9
                        }.step(ctx)
                    }
                }
            },
            _ => {
                let minors = Nil::<Expr>.alloc(ctx);
                MkMinorsGroup::Base {
                    checked_indblock : self.as_ptr(),
                    motives : self.motives(),
                    ind_name,
                    ind_type,
                    ind_const,
                    ctor_idx,
                    rem_ctor_names,
                    rem_ctor_types,
                    minors
                }.step(ctx)
            }

        }
    }        
    
    pub fn mk_minors_aux(
        &self, 
        ins : NamesPtr<'l>,
        its : ExprsPtr<'l>,
        ics : ExprsPtr<'l>,
        nums_ctors : &[u16],
        cns : NamesPtr<'l>,
        cts : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<MkMinorsAuxZst>) {
        match (ins.read(ctx), its.read(ctx), ics.read(ctx), nums_ctors) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [nc, ncs @ ..]) => {
                let cn_l = cns.take(*nc as usize, ctx);
                let cn_r = cns.skip(*nc as usize, ctx);

                let ct_l = cts.take(*nc as usize, ctx);
                let ct_r = cts.skip(*nc as usize, ctx);

                let (minors_r, h1) = self.mk_minors_aux(i_ns, i_ts, i_cs, ncs, cn_r, ct_r, ctx);
                let (minors_l, h2) = self.mk_minors_group(i_n, i_t, i_c, cn_l, ct_l, 1, ctx);
                let minors = minors_l.concat(minors_r, ctx);

                MkMinorsAux::Step {
                    checked_indblock : self.as_ptr(),
                    motives : self.motives(),
                    ind_names_hd : i_n,
                    ind_names_tl : i_ns,
                    ind_types_hd : i_t,
                    ind_types_tl : i_ts,
                    ind_consts_hd : i_c,
                    ind_consts_tl : i_cs,
                    ctor_names_l : cn_l,
                    ctor_names_r : cn_r,
                    ctor_types_l : ct_l,
                    ctor_types_r : ct_r,
                    minors_l,
                    minors_r,
                    ind_names : ins,
                    ind_types : its,
                    ind_consts : ics,
                    ctor_names : cns,
                    ctor_types : cts,
                    minors,
                    h1,
                    h2
                }.step(ctx)
            },
            (Nil, Nil, Nil, []) => {
                let minors = Nil::<Expr>.alloc(ctx);
                MkMinorsAux::Base {
                    checked_indblock : self.as_ptr(),
                    motives : self.motives(),
                    ind_names : ins,
                    ind_types : its,
                    ind_consts : ics,
                    ctor_names : cns,
                    ctor_types : cts,
                    minors
                }.step(ctx)

            }
            _ => unreachable!()
        }
    }

    pub fn mk_minors(&mut self, ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) -> Step<MkMinorsZst> {
        let (minors, h1) = self.mk_minors_aux(
            self.ind_names, 
            self.ind_types, 
            self.ind_consts, 
            self.nums_ctors.as_slice(),
            self.ctor_names, 
            self.ctor_types, 
            ctx
        );

        self.minors = Some(minors);
        MkMinors::Base {
            checked_indblock : self.as_ptr(),
            motives : self.motives(),
            all_minors : minors,
            h1,
        }.step_only(ctx)
    }    

    pub fn get_rec_levels(
        &self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (LevelsPtr<'l>, Step<GetRecLevelsZst>) {
        let (elim_level, h1) = self.elim_level();
        match self.elim_level().0.read(ctx) {
            Level::Param(n) => {
                let result = Cons(elim_level, self.uparams).alloc(ctx);
                GetRecLevels::Param {
                    checked_indblock : self.as_ptr(),
                    n,
                    elim_level,
                    rec_levels : result,
                    h1
                }.step(ctx)
            }
            _ => {
                GetRecLevels::NotParam {
                    checked_indblock : self.as_ptr(),
                    elim_level,
                    rec_levels : self.uparams,
                    h1
                }.step(ctx)
            }
        }
    }    

    pub fn handle_rec_args_rule(
        &self,
        ind_name : NamePtr<'l>,
        rem_rec_args : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (ExprsPtr<'l>, Step<HandleRecArgsRuleZst>) {
        match rem_rec_args.read(ctx) {
            Cons(hd, tl) => {
                let (result_tl, h1) = self.handle_rec_args_rule(ind_name, tl, ctx);

                let (u_i_ty_unred, h2) = hd.infer(InferOnly, &mut ctx.as_tc(None, None));
                let (u_i_ty_red, h3) = u_i_ty_unred.whnf(&mut ctx.as_tc(Some(self.uparams), None));

                let ((u_i_ty, xs), h4) = self.handle_rec_args_aux(u_i_ty_red, ctx);

                let ((valid_app, indices_result), h5) = self.get_i_indices(u_i_ty, ctx);
                
                let rec_name = ind_name.new_str(format!("rec"), ctx);

                let (rec_levels, h6) = self.get_rec_levels(ctx);
                let appA = <ExprPtr>::new_const(rec_name, rec_levels, ctx);
                
                let (appB, h7) = appA.foldl_apps(self.local_params, ctx);
                let (appC, h8) = appB.foldl_apps(self.motives(), ctx);
                let (appD, h9) = appC.foldl_apps(self.minors(), ctx);
                let (appE, h10) = appD.foldl_apps(indices_result, ctx);

                let (app_rhs, h11) = hd.foldl_apps(xs, ctx);
                let app = appE.new_app(app_rhs, ctx);

                let (v_hd, h12) = xs.fold_lambdas(app, ctx);

                let result = Cons(v_hd, result_tl).alloc(ctx);
                HandleRecArgsRule::Step {
                    checked_indblock : self.as_ptr(),
                    ind_name,
                    motives : self.motives(),
                    minors : self.minors(),
                    rec_args_hd : hd,
                    rec_args_tl : tl,
                    rec_rule_parts_hd : v_hd,
                    rec_rule_parts_tl : result_tl,
                    u_i_ty_unred,
                    u_i_ty_red,
                    u_i_ty,
                    xs,
                    valid_app,
                    indices_result,
                    elim_level : self.elim_level().0,
                    rec_levels,
                    appB,
                    appC,
                    appD,
                    appE,
                    app_rhs,
                    rec_args : rem_rec_args,
                    rec_rule_parts : result,
                    rec_name,
                    appA,
                    made_app : app,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5,
                    h6,
                    h7,
                    h8,
                    h9,
                    h10,
                    h11,
                    h12
                }.step(ctx)
            },
            Nil => {
                let result = rem_rec_args;
                HandleRecArgsRule::Base {
                    checked_indblock : self.as_ptr(),
                    ind_name,
                    rec_args : rem_rec_args,
                    rec_rule_parts : result
                }.step(ctx)
            }
        }
    }    

    pub fn mk_rec_rule1(
        &self, 
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        ctor_name : NamePtr<'l>,
        ctor_type : ExprPtr<'l>,
        // vv The whole group of minors
        minors_group : ExprsPtr<'l>,
        // vv minor corresponding to the constructor's index
        this_minor : ExprPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (RecRulePtr<'l>, Step<MkRecRule1Zst>) {
        let ((all_args, rec_args, inner), h1) = self.sep_rec_ctor_args(
            ind_type,
            ind_const,
            ctor_type,
            self.local_params,
            ctx
        );
        
        let (rec_rule_parts, h2) = self.handle_rec_args_rule(ind_name, rec_args, ctx);

        let (rhsA, h3) = this_minor.foldl_apps(all_args, ctx);
        let (rhsB, h4) = rhsA.foldl_apps(rec_rule_parts, ctx);
        let (rhsC, h5) = all_args.fold_lambdas(rhsB, ctx);
        let (rhsD, h6) = minors_group.fold_lambdas(rhsC, ctx);
        let (rhsE, h7) = self.motives().fold_lambdas(rhsD, ctx);
        let (rhsF, h8) = self.local_params.fold_lambdas(rhsE, ctx);
        let (tel_size, h9) = ctor_type.telescope_size(ctx);
        let num_fields = tel_size - self.num_params;
        let rec_rule = RecRule::new(ctor_name, num_fields, rhsF).alloc(ctx);
        MkRecRule1::Base {
            checked_indblock : self.as_ptr(),
            motives : self.motives(),
            ind_name,
            ind_type,
            ind_const,
            ctor_name,
            ctor_type,
            minors_group,
            this_minor,
            all_args,
            rec_args,
            inner,
            rec_rule_parts,
            rhsA,
            rhsB,
            rhsC,
            rhsD,
            rhsE,
            rhsF,
            tel_size,
            num_fields,
            rec_rule,
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
            h7,
            h8,
            h9
        }.step(ctx)
    }    


    pub fn mk_rec_rules1group(
        &mut self,
        ind_name : NamePtr<'l>,
        ind_type : ExprPtr<'l>,
        ind_const : ExprPtr<'l>,
        rem_ctor_names : NamesPtr<'l>,
        rem_ctor_types : ExprsPtr<'l>,
        minors_group : ExprsPtr<'l>,
        rem_minors : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (RecRulesPtr<'l>, Step<MkRecRulesGroupZst>) {
        match (rem_ctor_names.read(ctx), rem_ctor_types.read(ctx), rem_minors.read(ctx)) {
            (Cons(n, ns), Cons(t, ts), Cons(m, ms)) => {
                let (rec_rules_tl, h1) = self.mk_rec_rules1group(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    ns, 
                    ts, 
                    minors_group, 
                    ms, 
                    ctx
                );
                let (rec_rules_hd, h2) = self.mk_rec_rule1(
                    ind_name, 
                    ind_type, 
                    ind_const, 
                    n, 
                    t, 
                    minors_group, 
                    m, 
                    ctx
                );
                let rec_rules = Cons(rec_rules_hd, rec_rules_tl).alloc(ctx);
                MkRecRulesGroup::Step {
                    indblock : self.as_ptr(),
                    motives : self.motives(),
                    ind_name,
                    ind_type,
                    ind_const,
                    minors_group,
                    rem_ctor_names_hd : n,
                    rem_ctor_names_tl : ns,
                    rem_ctor_types_hd : t,
                    rem_ctor_types_tl : ts,
                    rem_minors_hd : m,
                    rem_minors_tl : ms,
                    rec_rules_hd,
                    rec_rules_tl,
                    rem_ctor_names,
                    rem_ctor_types,
                    rem_minors,
                    rec_rules,
                    h1,
                    h2
                }.step(ctx)
            },
            (Nil, Nil, Nil) => {
                let rec_rules = Nil::<RecRule>.alloc(ctx);
                MkRecRulesGroup::Base {
                    indblock : self.as_ptr(),
                    motives : self.motives(),
                    ind_name,
                    ind_type,
                    ind_const,
                    minors_group,
                    rem_ctor_names,
                    rem_ctor_types,
                    rem_minors,
                    rec_rules,
                }.step(ctx)
            }
            _ => unreachable!("Uneven list lengths in mk_rec_rules1group")
        }

    }    


    // ind_names
    // ind_types
    // ind_consts
    // nums_ctors
    // ctor_names
    // ctor_types
    // minors
    pub fn mk_rec_rules(
        &mut self, 
        ind_names : NamesPtr<'l>,
        ind_types : ExprsPtr<'l>,
        ind_consts : ExprsPtr<'l>,
        nscs : &[u16],
        ctor_names : NamesPtr<'l>,
        ctor_types : ExprsPtr<'l>,
        minors : ExprsPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (RecRulesPtr<'l>, Step<MkRecRulesZst>) {

        match (ind_names.read(ctx), ind_types.read(ctx), ind_consts.read(ctx), nscs) {
            (Cons(i_n, i_ns), Cons(i_t, i_ts), Cons(i_c, i_cs), [num, nums @ ..]) => {
                let ctor_names_l = ctor_names.take(*num as usize, ctx);
                let ctor_names_r = ctor_names.skip(*num as usize, ctx);

                let ctor_types_l = ctor_types.take(*num as usize, ctx);
                let ctor_types_r = ctor_types.skip(*num as usize, ctx);

                let minors_l = minors.take(*num as usize, ctx);
                let minors_r = minors.skip(*num as usize, ctx);

                let (rec_rules_r, h1) = self.mk_rec_rules(
                    i_ns, 
                    i_ts, 
                    i_cs, 
                    nums, 
                    ctor_names_r, 
                    ctor_types_r, 
                    minors_r, 
                    ctx
                );

                let (rec_rules_l, h2) = self.mk_rec_rules1group(
                    i_n, 
                    i_t, 
                    i_c, 
                    ctor_names_l, 
                    ctor_types_l, 
                    minors_l, 
                    minors_l, 
                    ctx
                );

                let rec_rules = rec_rules_l.concat(rec_rules_r, ctx);
                MkRecRules::Step {
                    indblock : self.as_ptr(),
                    all_motives : self.motives(),
                    ind_names_hd : i_n,
                    ind_names_tl : i_ns,
                    ind_types_hd : i_t,
                    ind_types_tl : i_ts,
                    ind_consts_hd : i_c,
                    ind_consts_tl : i_cs,
                    ctor_names_l,
                    ctor_names_r,
                    ctor_types_l,
                    ctor_types_r,
                    minors_l,
                    minors_r,
                    rec_rules_l,
                    rec_rules_r,
                    ind_names,
                    ind_types,
                    ind_consts,
                    ctor_names,
                    ctor_types,
                    minors,
                    rec_rules,
                    h1,
                    h2
                }.step(ctx)
            },

            (Nil, Nil, Nil, []) => {
                let rec_rules = Nil::<RecRule>.alloc(ctx);
                MkRecRules::Base {
                    indblock : self.as_ptr(),
                    all_motives : self.motives(),
                    ind_names,
                    ind_types,
                    ind_consts,
                    ctor_names,
                    ctor_types,
                    minors,
                    rec_rules
                }.step(ctx)
            }
            _ => unreachable!("Bad match in mk_rec_rules")

        }
    }    

    
    // This is just for mutable state; doesn't appear in the spec.
    pub fn declare_rec_rules(
        &mut self, 
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> Step<MkRecRulesZst> {
        let (rec_rules, h1) = self.mk_rec_rules(
            self.ind_names,
            self.ind_types,
            self.ind_consts,
            self.nums_ctors.clone().as_slice(),
            self.ctor_names,
            self.ctor_types,
            self.minors(),
            ctx
        );

        self.rec_rules = Some(rec_rules);
        h1
    }    

    // FIXME remove num_indices
    pub fn mk_recursor_aux(
        &self, 
        ind_name : NamePtr<'l>,
        num_indices : u16,
        motive : ExprPtr<'l>,
        major : ExprPtr<'l>,
        local_indices : ExprsPtr<'l>,
        minors : ExprsPtr<'l>,
        rec_rules : RecRulesPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (DeclarPtr<'l>, Step<MkRecursorAuxZst>) {
        assert_eq!(num_indices as usize, local_indices.len(ctx));
        let num_minors = minors.len(ctx) as u16;
        let num_motives = self.motives().len(ctx) as u16;
        let rec_name = ind_name.new_str(format!("rec"), ctx);

        let (motive_app_base, h1) = motive.foldl_apps(local_indices, ctx);

        let motive_app = if self.use_dep_elim() {
            motive_app_base.new_app(major, ctx)
        } else {
            motive_app_base
        };


        let (tyA, h2) = major.apply_pi(motive_app, ctx);
        let (tyB, h3) = local_indices.fold_pis(tyA, ctx);
        let (tyC, h4) = minors.fold_pis(tyB, ctx);
        let (tyD, h5) = self.motives().fold_pis(tyC, ctx);
        let (rec_ty, h6) = self.local_params.fold_pis(tyD, ctx);
        let (rec_uparams, h7) = self.get_rec_levels(ctx);
        let major_idx = self.num_params + num_indices + num_minors + num_motives;


        let r = <DeclarPtr>::new_recursor(
            rec_name,
            rec_uparams,
            rec_ty,
            self.ind_names,
            self.num_params,
            num_indices,
            num_motives,
            num_minors as u16,
            major_idx,
            rec_rules,
            self.k_target(),
            self.is_unsafe,
            ctx
        );
        
        if !self.use_dep_elim() {
            MkRecursorAux::BaseIndep {
                indblock : self.as_ptr(),
                ind_name,
                all_motives : self.motives(),
                motive,
                major,
                minors,
                rec_rules,
                k_target : self.k_target(),
                elim_level : self.elim_level().0,
                motive_app,
                tyA,
                tyB,
                tyC,
                tyD,
                rec_ty,
                rec_uparams,
                num_indices,
                num_minors,
                num_motives,
                major_idx,
                rec_name,
                recursor : r,
                h1,
                h2,
                h3,
                h4,
                h5,
                h6,
                h7
            }.step(ctx)
        } else {
             MkRecursorAux::BaseDep {
                indblock : self.as_ptr(),
                ind_name,
                all_motives : self.motives(),
                motive,
                major,
                minors,
                rec_rules,
                k_target : self.k_target(),
                elim_level : self.elim_level().0,
                motive_app_base,
                tyA,
                tyB,
                tyC,
                tyD,
                rec_ty,
                rec_uparams,
                num_indices,
                num_minors,
                num_motives,
                major_idx,
                rec_name,
                motive_app,
                recursor : r,
                h1,
                h2,
                h3,
                h4,
                h5,
                h6,
                h7
            }.step(ctx)           
        }
    }    


    pub fn mk_recursors(
        &self, 
        ind_names : NamesPtr<'l>,
        nums_ctors : &[u16],
        nums_indices : &[u16],
        motives : ExprsPtr<'l>,
        majors : ExprsPtr<'l>,
        local_indices : ExprsPtr<'l>,
        minors : ExprsPtr<'l>,
        rec_rules : RecRulesPtr<'l>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) -> (DeclarsPtr<'l>, Step<MkRecursorsZst>) {
        match (
            ind_names.read(ctx), 
            nums_ctors, 
            nums_indices, 
            motives.read(ctx), 
            majors.read(ctx)
        ) {
            (Cons(n, ns), 
             [num, nums @ ..], 
             [li, lis @ ..], 
             Cons(mo, mos), 
             Cons(ma, mas)) => {
                let minors_l = minors.take(*num as usize, ctx);
                let minors_r = minors.skip(*num as usize, ctx);

                let rec_rules_l = rec_rules.take(*num as usize, ctx);
                let rec_rules_r = rec_rules.skip(*num as usize, ctx);

                let indices_l = local_indices.take(*li as usize, ctx);
                let indices_r = local_indices.skip(*li as usize, ctx);

                let (recursors_tl, h1) = self.mk_recursors(
                    ns, 
                    nums, 
                    lis, 
                    mos, 
                    mas, 
                    indices_r, 
                    minors_r, 
                    rec_rules_r, 
                    ctx
                );

                let (recursors_hd, h2) = self.mk_recursor_aux(
                    n, 
                    *li,
                    mo, 
                    ma, 
                    indices_l, 
                    minors_l, 
                    rec_rules_l, 
                    ctx
                );

                let recursors = Cons(recursors_hd, recursors_tl).alloc(ctx);
                MkRecursors::Step {
                    indblock : self.as_ptr(),
                    all_motives : self.motives(),
                    k_target : self.k_target(),
                    elim_level : self.elim_level().0,
                    ind_names_hd : n,
                    ind_names_tl : ns,
                    motives_hd : mo,
                    motives_tl : mos,
                    majors_hd : ma,
                    majors_tl : mas,
                    minors_l,
                    minors_r,
                    indices_l,
                    indices_r,
                    rec_rules_l,
                    rec_rules_r,
                    recursors_hd,
                    recursors_tl,
                    num_indices : indices_l.len(ctx) as u16,
                    ind_names,
                    motives,
                    majors,
                    indices : local_indices,
                    minors,
                    rec_rules,
                    recursors,
                    h1,
                    h2
                }.step(ctx)
            },
            (Nil, [], [], Nil, Nil) => {
                let recursors = Nil::<Declar>.alloc(ctx);
                 MkRecursors::Base {
                    indblock : self.as_ptr(),
                    all_motives : self.motives(),
                    k_target : self.k_target(),
                    elim_level : self.elim_level().0,
                    ind_names,
                    motives,
                    majors,
                    minors,
                    indices : local_indices,
                    rec_rules,
                    recursors
                 }.step(ctx)
            }
            _ => panic!("declare recursors must receive lists with equal lengths")
        }
    }

    pub fn declare_recursors(
        &mut self, 
        h1 : Step<MkElimLevelZst>,
        h2 : Step<InitKTargetZst>,
        h3 : Step<MkMajorsAuxZst>,
        h4 : Step<MkMotivesZst>,
        h5 : Step<MkMinorsZst>,
        h6 : Step<MkRecRulesZst>,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>) {
        let(recursors, h7) = self.mk_recursors(
            self.ind_names, 
            self.nums_ctors.as_slice(),
            self.nums_indices.as_slice(),
            self.motives(), 
            self.majors(), 
            self.local_indices, 
            self.minors(), 
            self.rec_rules(),
            ctx
        );

        let step = AdmitDeclar::Recursors {
            env : ctx.last_admit().expect("Recursor"),
            checked_indblock : self.as_ptr(),
            recursors,
            majors : self.majors(),
            motives : self.motives(),
            minors : self.minors(),
            indices : self.local_indices,
            elim_level : self.elim_level().0,
            k_target : self.k_target(),
            rec_rules : self.rec_rules(),
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
            h7
        }.step_only(ctx);

        assert_eq!(self.ctor_names.len(ctx), self.minors().len(ctx));
        assert_eq!(self.ctor_names.len(ctx), self.rec_rules().len(ctx));
        assert_eq!(self.ind_types.len(ctx), recursors.len(ctx));
        ctx.admit_declars(recursors, step);
    }
}
