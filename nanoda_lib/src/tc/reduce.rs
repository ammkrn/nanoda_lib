use nanoda_macros::has_try;
use crate::{ exprs, ret_none_if };
use crate::name::{ NamePtr, NamesPtr };
use crate::level::{ LevelPtr, Level, LevelsPtr };
use crate::expr::{ Expr, Expr::*, ExprPtr, ExprsPtr, BinderStyle::* };
use crate::env::{ Declar::*, DeclarPtr, ReducibilityHint::* };
use crate::tc::infer::InferFlag::*;
use crate::tc::eq::ShortCircuit::*;
use crate::trace::IsTracer;
use crate::trace::steps::*;
use crate::utils::{ 
    IsTc, 
    IsCtx, 
    IsLiveCtx, 
    List, 
    List::*, 
    Ptr, 
    ListPtr, 
    Store, 
    Env, 
    Live, 
    EnvZst, 
    LiveZst, 
    HasMkPtr, 
    Set, 
    HasNanodaDbg 
};




impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {


    #[has_try(method = "self.unfold_def(tc)")]
    pub fn unfold_def(
        self, 
        tc : &mut impl IsTc<'t, 'l, 'e>,
        //safety_tok : (),
    ) -> Option<(ExprPtr<'l>, Step<UnfoldDef<'l>>)> {
        let ((fun, args), h1) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let (def, h2) = tc.get_declar(c_name)?;
        match def.read(tc) {
            Definition { uparams, type_, val, hint, is_unsafe, .. } => {
                let (c_levels_len, h3) = c_levels.len(tc);
                let (uparams_len, h4) = uparams.len(tc);
                if c_levels_len == uparams_len {
                    let (val_prime, h5) = val.subst(uparams, c_levels, tc);
                    let (e_prime, h6) = val_prime.foldl_apps(args, tc);
                    Some(UnfoldDef::Base {
                        e : self,
                        c_name,
                        c_levels,
                        args,
                        uparams,
                        type_,
                        val,
                        hint,
                        is_unsafe,
                        uparams_len,
                        val_prime,
                        e_prime,
                        h1,
                        h2,
                        h3,
                        h4,
                        h5,
                        h6
                    }.step(tc))
                } else {
                    None
                }
            },
            _ => None
        }        
    }    

    pub fn whnf_lambda(
        self,
        rem_args : ExprsPtr<'l>,
        lambda_args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (ExprPtr<'l>, Step<WhnfLambda<'l>>) {
        match (self.read(tc), rem_args.read(tc)) {
            (Lambda { b_name, b_type, b_style, body, .. }, Cons(hd, tl)) => {
                let (e_prime, h1) = body.whnf_lambda(
                    tl, 
                    Cons(hd, lambda_args).alloc(tc),
                    tc
                );
                WhnfLambda::Step {
                    b_name,
                    b_type,
                    b_style,
                    body,
                    hd,
                    tl,
                    lambda_args,
                    e_prime,
                    h1,
                    ind_arg1 : self,
                    ind_arg2 : rem_args,
                }.step(tc)
            }
            (_, Cons(..)) => {
                let (b, h1) = self.is_lambda(tc);
                assert!(!b);
                let (e_B, h2) = self.inst(lambda_args, tc);
                let (e_C, h3) = e_B.foldl_apps(rem_args, tc);
                let (e_D, h4) = e_C.whnf_core(tc);
                WhnfLambda::NotLambda {
                    e_A : self,
                    rem_args,
                    lambda_args,
                    e_B,
                    e_C,
                    e_D,
                    h1,
                    h2,
                    h3,
                    h4,
                }.step(tc)
            },
            (_, Nil) => {
                let (e_B, h1) = self.inst(lambda_args, tc);
                let (e_C, h2) = e_B.whnf_core(tc);
                WhnfLambda::NoArgs {
                    e_A : self,
                    lambda_args,
                    e_B,
                    e_C,
                    h1,
                    h2,
                    ind_arg2 : rem_args,
                }.step(tc)
            }
        }
    }

    pub fn whnf_sort(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (ExprPtr<'l>, Step<WhnfSort<'l>>) {
        match self.read(tc) {
            Sort { level } => {
                let (l_prime, h1) = level.simplify(tc);
                WhnfSort::Base {
                    l : level,
                    l_prime,
                    h1,
                    ind_arg1 : self,
                    ind_arg2 : l_prime.new_sort(tc)
                }.step(tc)
            },
            _ => unreachable!("Checked pattern match; whnf_sort")
        }
    }

    pub fn whnf_let(
        self,
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<WhnfLet<'l>>) {
        match self.read(tc) {
            Let { b_name, b_type, b_style, val, body : body_A, .. } => {
                let (body_B, h1) = body_A.inst1(val, tc);
                let (body_C, h2) = body_B.foldl_apps(args, tc);
                let (body_D, h3) = body_C.whnf_core(tc);
                WhnfLet::Base {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body_A,
                    args,
                    body_B,
                    body_C,
                    body_D,
                    h1,
                    h2,
                    h3,
                    ind_arg1 : self
                }.step(tc)
            },
            _ => unreachable!("Checked pattern match; whnf_let")
        }
    }

    // What we're looking for is an application of quot.lift,
    // which has type : 
    // quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
    //   (∀ (a b : A), r a b → f a = f b) → @quot A r → B      
    // So (qmk_pos := 5) points to the 5th (starting from 0) element,
    // which is (quot.mk (A : Sort u) (r : A -> A -> Prop) (a : A))
    // which gets us our (@quot A r)
    // and then (f_pos := 3) is the (f : A -> B) item.
    // There are a bunch of boring checks, but basically we just pull out
    // the (f), pull the (a : A) out of the application of (quot.mk)
    // and then apply it, fold back up the extra arguments if they exist,
    // and keep reducing.
    #[has_try(method = "self.reduce_quot_lift(args, tc)")]
    fn reduce_quot_lift(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ReduceQuotLift<'l>>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;
        let (qmk_n, qlift_n, _) = tc.quot_names()?;
        let (qmk_pos, f_pos) = if c_name == qlift_n { (5, 3) } else { return None };
        let (qmk_A_r_a_unred, h1) = match args.get(qmk_pos, tc) {
            (None, _) => return None,
            (Some(qmk_unred), h1) => (qmk_unred, h1)
        };

        let (qmk_A_r_a, h2) = qmk_A_r_a_unred.whnf(tc);

        let ((qmk_const, qmk_args), h3) = qmk_A_r_a.unfold_apps(tc);
        let (qmk_const_name, qmk_const_levels) = qmk_const.try_const_info(tc)?;
        if qmk_const_name != qmk_n {
            return None
        }

        // (f : A -> B)
        let (f, h4) = match args.get(f_pos, tc) {
            (None, _) => return None,
            (Some(f), h4) => (f, h4)
        };

        let a = match qmk_A_r_a.read(tc) {
            App { arg : a, .. } => a,
            _ => unreachable!("Bad quot_rec (lift) app")
        };

        let B = f.new_app(a, tc);

        let (skipped, h5) = args.skip(qmk_pos + 1, tc);
        let (out_unred, h6) = B.foldl_apps(skipped, tc);
        let (out, h7) = out_unred.whnf_core(tc);
        Some(ReduceQuotLift::Base {
            c_levels,
            args,
            qmk_A_r_a_unred,
            qmk_A_r_a,
            f,
            a,
            qmk_levels : qmk_const_levels,
            qmk_args,
            skipped,
            out_unred,
            out,
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
            h7,
            ind_arg1 : self,
        }.step(tc))
    }        

    
    // This is almost identical to reduce_quot_lift, but after extracting
    // (a : A) from quotmk_A_r_a, instead of applying it to argument # 5,
    // (f : A -> B) we're applying it to argument # 4, 
    // which is `(∀ (a : A), B (@quot.mk A r a))`
    #[has_try(method = "self.reduce_quot_ind(args, tc)")]
    fn reduce_quot_ind(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ReduceQuotInd<'l>>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;
        let (qmk_n, _, qind_n) = tc.quot_names()?;
        let (qmk_pos, B_of_pos) = if c_name == qind_n { (4, 3) } else { return None };

        
        let (qmk_A_r_a_unred, h1) = match args.get(qmk_pos, tc) {
            (None, _) => return None,
            (Some(qmk_unred), h1) => (qmk_unred, h1)
        };
        
        let (qmk_A_r_a, h2) = qmk_A_r_a_unred.whnf(tc);

        let ((qmk_const, qmk_args), h3) = qmk_A_r_a.unfold_apps(tc);
        let (qmk_const_name, qmk_const_levels) = qmk_const.try_const_info(tc)?;
        if qmk_const_name != qmk_n {
            return None
        }


        let (B_of, h4) = match args.get(B_of_pos, tc) {
            (None, _) => return None,
            (Some(B_of), h4) => (B_of, h4)
        };

        let a = match qmk_A_r_a.read(tc) {
            App { arg : a, .. } => a,
            _ => unreachable!("Bad quot_rec (lift) app")
        };
        
        let B_app = B_of.new_app(a, tc);

        let (skipped, h5) = args.skip(qmk_pos + 1, tc);
        let (out_unred, h6) = B_app.foldl_apps(skipped, tc);
        let (out, h7) = out_unred.whnf_core(tc);

        Some(ReduceQuotInd::Base {
            c_levels,
            args,
            qmk_A_r_a_unred,
            qmk_A_r_a,
            B_of,
            a,
            qmk_levels : qmk_const_levels,
            qmk_args,
            skipped,
            out_unred,
            out,
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
            h7,
            ind_arg1 : self,
        }.step(tc))

    }        

    fn mk_nullary_ctor(
        self,
        num_params : u16, 
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<MkNullaryCtor<'l>>)> {
        let ((fun, args), h1) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let (dptr, h2) = tc.get_declar(c_name)?;

        let (
            zth_ctor_name, 
            d_uparams,
            d_type,
            d_all_ind_names,
            d_all_ctor_names,
            d_is_unsafe,
            h3
        ) = match dptr.read(tc) {
            Inductive { 
                uparams : d_uparams, 
                type_ : d_type,
                all_ind_names,
                all_ctor_names, 
                is_unsafe,
                .. 
            } => match all_ctor_names.get(0, tc) {
                (None, _) => return None,
                (Some(n), h3) => (
                    n, 
                    d_uparams,
                    d_type,
                    all_ind_names,
                    all_ctor_names,
                    is_unsafe,
                    h3
                )
            }
            _ => return None
        };

        let made_const = <ExprPtr>::new_const(zth_ctor_name, c_levels, tc);
        let (fold_args, h4) = args.take(num_params as usize, tc);
        let (out, h5) = made_const.foldl_apps(fold_args, tc);
        Some(MkNullaryCtor::Base {
            e : self,
            num_params,
            fun_name : c_name,
            fun_levels : c_levels,
            args,
            d_uparams,
            d_type,
            d_all_ind_names,
            d_all_ctor_names,
            d_is_unsafe,
            zth_ctor_name,
            fold_args,
            out,
            h1,
            h2,
            h3,
            h4,
            h5
        }.step(tc))
    }    

    // Either returns the altered major or returns the original major.
    fn to_ctor_when_k(
        self,
        recursor : DeclarPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<ToCtorWhenK<'l>>) {
        if let Some(pair) = self.to_ctor_when_k_aux(recursor, tc) {
            pair
        } else {
            ToCtorWhenK::Skip {
                e : self,
            }.step(tc)
        }
    }

    fn to_ctor_when_k_aux(
        self,
        recursor : DeclarPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ToCtorWhenK<'l>>)> {
        ret_none_if! { !recursor.rec_is_k(tc)? };
        let (e_type_unred, h1) = self.infer(InferOnly, tc);
        let (e_type, h2) = e_type_unred.whnf(tc);

        
        let ((e_t_fun, e_t_levels), _) = e_type.unfold_apps(tc);
        ret_none_if! { 
            e_t_fun.try_const_info(tc)?.0 != recursor.name(tc).get_prefix(tc).0 
        };

        let (new_ctor_app, h3) = e_type.mk_nullary_ctor(recursor.rec_num_params(tc)?, tc)?;
        let (new_type, h4) = new_ctor_app.infer(InferOnly, tc);
        let (eq_result, h5) = e_type.def_eq(new_type, tc);

        if let EqShort = eq_result {
            Some(ToCtorWhenK::Base {
                e : self,
                name : recursor.name(tc),
                uparams : recursor.uparams(tc),
                type_ : recursor.type_(tc),
                all_names : recursor.rec_all_names(tc).unwrap(),
                num_params : recursor.rec_num_params(tc).unwrap(),
                num_indices : recursor.rec_num_indices(tc).unwrap(),
                num_motives : recursor.rec_num_motives(tc).unwrap(),
                num_minors : recursor.rec_num_minors(tc).unwrap(),
                major_idx : recursor.rec_major_idx(tc).unwrap(),
                rec_rules : recursor.rec_rules(tc).unwrap(),
                is_k : recursor.rec_is_k(tc).unwrap(),
                is_unsafe : recursor.is_unsafe(tc),
                e_type_unred,
                e_type,
                new_ctor_app,
                new_type,
                h1,
                h2,
                h3,
                h4,
                h5,
            }.step(tc))
        } else {
            None
        }
    }

    #[has_try(method = "self.reduce_ind_rec(args, tc)")]
    fn reduce_ind_rec(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ReduceIndRec<'l>>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;

        let (recursor, h1) = tc.get_declar(c_name)?;
        match recursor.read(tc) {
            Recursor {..} => (),
            _ => return None
        }


        ret_none_if! { recursor.rec_major_idx(tc)? as usize >= args.len(tc).0 };
        ret_none_if! { c_levels.len(tc).0 != recursor.uparams(tc).len(tc).0 };

        let (major_unred0, h2) = match args.get(recursor.rec_major_idx(tc)? as usize, tc) {
            (None, _) => return None,
            (Some(m), h2) => (m, h2)

        };

       let (major_unred, h3) = major_unred0.to_ctor_when_k(recursor, tc);
       let (major, h4) = major_unred.whnf(tc);
       let ((major_fun, major_args), h5) = major.unfold_apps(tc);
       let (rec_rule, h6) = recursor.rec_rules(tc)?.get_rec_rule(major, tc)?;

       let (major_args_len, h7) = major_args.len(tc);
       let sub_num_params = major_args_len.checked_sub(rec_rule.read(tc).num_fields as usize)?;


        let take_size = recursor.rec_num_params(tc)?
                      + recursor.rec_num_motives(tc)?
                      + recursor.rec_num_minors(tc)?;       
       // NOT USED AFTER
       let (skip1, h8) = major_args.skip(sub_num_params, tc);
       // end_apps
       let (take1, h9) = skip1.take(rec_rule.read(tc).num_fields as usize, tc);

       let (skip2, h10) = args.skip((recursor.rec_major_idx(tc)? + 1) as usize , tc);
       let (take2, h11) = args.take(take_size as usize, tc);

       let (r12, h12) = rec_rule.read(tc).val.subst(recursor.uparams(tc), c_levels, tc);
       let (r13, h13) = r12.foldl_apps(take2, tc);
       let (r14, h14) = r13.foldl_apps(take1, tc);
       let (r15, h15) = r14.foldl_apps(skip2, tc);
       let (out, h16) = r15.whnf_core(tc);

       Some(ReduceIndRec::Base {
           c_name,
           c_levels,
           name : recursor.name(tc),
           uparams : recursor.uparams(tc),
           type_ : recursor.type_(tc),
           all_names : recursor.rec_all_names(tc).unwrap(),
           num_params : recursor.rec_num_params(tc).unwrap(),
           num_indices : recursor.rec_num_indices(tc).unwrap(),
           num_motives : recursor.rec_num_motives(tc).unwrap(),
           num_minors : recursor.rec_num_minors(tc).unwrap(),
           major_idx : recursor.rec_major_idx(tc).unwrap(),
           rec_rules : recursor.rec_rules(tc).unwrap(),
           is_k : recursor.rec_is_k(tc).unwrap(),
           is_unsafe : recursor.is_unsafe(tc),           
           rr_name : rec_rule.read(tc).ctor_name,
           rr_n_fields : rec_rule.read(tc).num_fields,
           rr_val : rec_rule.read(tc).val,
           major_unred0,
           major_unred,
           major,
           major_fun,
           major_args,
           rec_rule,
           major_args_len,
           skip1,
           take1,
           skip2,
           take2,
           r12,
           r13,
           r14,
           r15,
           out,
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
           h12,
           h13,
           h14,
           h15,
           h16,
       }.step(tc))
    }        


    pub fn whnf_core(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<WhnfCore<'l>>) {
        let ((fun, args), h1) = self.unfold_apps(tc);
        match (fun.read(tc), args.read(tc)) {
            (Sort { level }, Nil) => {
                let (e_prime, h2) = self.whnf_sort(tc);
                WhnfCore::Sort {
                    e : self,
                    l : level,
                    e_prime,
                    h1,
                    h2,
                }.step(tc)
            },
            (Lambda {..}, Cons(hd, tl)) => {
                let (e_prime, h2) = fun.whnf_lambda(args, exprs!([], tc), tc);
                WhnfCore::Lambda {
                    e : self,
                    lam : fun,
                    args,
                    e_prime,
                    h1,
                    h2,
                }.step(tc)
            },
            (Let {..}, _) => {
                let (e_prime, h2) = fun.whnf_let(args, tc);
                WhnfCore::Let {
                    e : self,
                    let_ : fun,
                    args,
                    e_prime,
                    h1,
                    h2,
                }.step(tc)
            },
            _ => {
                if let Some((e_prime, h_quot_lift)) = fun.try_reduce_quot_lift(args, tc) {
                    WhnfCore::ReduceQuotLift {
                        e : self,
                        e_prime,
                        h1 : h_quot_lift,
                    }.step(tc)
                } else if let Some((e_prime, h_quot_ind)) = fun.try_reduce_quot_ind(args, tc) {
                    WhnfCore::ReduceQuotInd {
                        e : self,
                        e_prime,
                        h1 : h_quot_ind
                    }.step(tc)
                } else if let Some((e_prime, h_ind_rec)) = fun.try_reduce_ind_rec(args, tc) {
                    WhnfCore::ReduceIndRec {
                        e : self,
                        e_prime,
                        h1 : h_ind_rec,
                    }.step(tc)
                } else {
                    WhnfCore::Owise {
                        e : self,
                    }.step(tc)
                }
            }
        }
    }


    pub fn whnf(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<Whnf<'l>>) {
        if let Some((cached, step)) = tc.check_whnf_cache(&self) {
            Whnf::CacheHit {
                e : self,
                e_prime : cached,
                h1 : step,
            }.step(tc)
        } else {
            let (whnf_cored, h1) = self.whnf_core(tc);
            if let Some((unfolded, h2)) = self.try_unfold_def(tc) {
                let (eD, h3) = unfolded.whnf(tc);
                Whnf::Unfolding{
                    eA : self,
                    eB : whnf_cored,
                    eC : unfolded,
                    eD,
                    h1,
                    h2,
                    h3,
                }.step(tc)
            } else {
                Whnf::CoreOnly {
                    e : self,
                    e_prime : whnf_cored,
                    h1,
                }.step(tc)
            }
        }
    }        

}

