use nanoda_macros::has_try_some;
use crate::{ exprs, ret_none_if };
use crate::expr::{ Expr, Expr::*, ExprPtr, ExprsPtr };
use crate::env::{ Declar::*, DeclarPtr };
use crate::tc::infer::InferFlag::*;
use crate::trace::steps::*;
use crate::utils::{ 
    IsTc, 
    List, 
    List::*, 
    //HasNanodaDbg 
};

use crate::tc::eq::EqResult::*;

impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    #[has_try_some(method = "self.unfold_def(tc)")]
    pub fn unfold_def(
        self, 
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> Option<(ExprPtr<'l>, Step<UnfoldDefZst>)> {
        let ((fun, args), h1) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let (d_view, h_admitted) = tc.get_declar_view(c_name)?;
        let h2 = (c_name, h_admitted, d_view);
        let d_val = d_view.val?;
        ret_none_if! { c_levels.len(tc) != d_view.uparams.len(tc) };

        let (d_val_prime, h3) = d_val.subst(d_view.uparams, c_levels, tc);
        let (unfolded, h4) = d_val_prime.foldl_apps(args, tc);

        Some(UnfoldDef::Base {
            e : self,
            c_name,
            c_levels,
            args,
            d_uparams : d_view.uparams,
            d_type : d_view.type_,
            d_val,
            d_val_prime,
            unfolded,
            base : fun,
            d_view,
            h1,
            h2,
            h3,
            h4
        }.step(tc))
    }    

    pub fn whnf_sort(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (ExprPtr<'l>, Step<WhnfSortZst>) {
        match self.read(tc) {
            Sort { level } => {
                let (l_prime, h1) = level.simplify(tc);
                WhnfSort::Base {
                    l : level,
                    l_prime,
                    s : self,
                    s_prime : l_prime.new_sort(tc),
                    h1,
                }.step(tc)
            },
            _ => unreachable!("Checked pattern match; whnf_sort")
        }
    }    

    pub fn whnf_lambda(
        self,
        rem_args : ExprsPtr<'l>,
        lambda_args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (ExprPtr<'l>, Step<WhnfLambdaZst>) {
        match (self.read(tc), rem_args.read(tc)) {
            (Lambda { b_name, b_type, b_style, body, .. }, Cons(hd, tl)) => {
                let lambda_args_prime = Cons(hd, lambda_args).alloc(tc);
                let (b_prime, h1) = body.whnf_lambda(
                    tl, 
                    lambda_args_prime,
                    tc
                );

                WhnfLambda::Step {
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    b : body,
                    arg_hd : hd,
                    args_tl : tl,
                    lambda_args,
                    b_prime,
                    lambda : self,
                    lambda_args_prime,
                    all_args : rem_args,
                    h1,
                }.step(tc)
            }
            (_, Cons(..)) => {
                let (b, h1) = self.is_lambda(tc);
                assert!(!b);
                let (eB, h2) = self.inst(lambda_args, tc);
                let (eC, h3) = eB.foldl_apps(rem_args, tc);
                let (eD, h4) = eC.whnf_core(tc);
                WhnfLambda::NotLambda {
                    eA : self,
                    rem_args,
                    lambda_args,
                    eB,
                    eC,
                    eD,
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
                    all_args : rem_args,
                    h1,
                    h2,
                }.step(tc)
            }
        }
    }



    pub fn whnf_let(
        self,
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<WhnfLetZst>) {
        match self.read(tc) {
            Let { b_name, b_type, b_style, val, body : bodyA, .. } => {
                let (bodyB, h1) = bodyA.inst1(val, tc);
                let (bodyC, h2) = bodyB.foldl_apps(args, tc);
                let (e_prime, h3) = bodyC.whnf_core(tc);
                WhnfLet::Base {
                    n : b_name,
                    t : b_type,
                    s : b_style,
                    v : val,
                    bodyA,
                    args,
                    bodyB,
                    bodyC,
                    e_prime,
                    e : self,
                    h1,
                    h2,
                    h3,
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
    #[has_try_some(method = "self.reduce_quot_lift(args, tc)")]
    fn reduce_quot_lift(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ReduceQuotLiftZst>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;
        let (qmk_n, qlift_n, _) = tc.quot_names()?;
        let (qmk_pos, f_pos) = if c_name == qlift_n { (5, 3) } else { return None };
        let qmk_A_r_a_unred = args.get(qmk_pos, tc)?;

        let (qmk_A_r_a, h1) = qmk_A_r_a_unred.whnf(tc);

        let ((qmk_const, qmk_args), h2) = qmk_A_r_a.unfold_apps(tc);
        let (qmk_const_name, qmk_const_levels) = qmk_const.try_const_info(tc)?;
        if qmk_const_name != qmk_n {
            return None
        }

        // (f : A -> B)
        let f = args.get(f_pos, tc)?;

        let (qmk_A_r, a) = match qmk_A_r_a.read(tc) {
            App { fun : qmk_A_r, arg : a, .. } => (qmk_A_r, a),
            _ => unreachable!("Bad quot_rec (lift) app")
        };

        let B = f.new_app(a, tc);

        let skipped = args.skip(qmk_pos + 1, tc);
        let (out_unred, h3) = B.foldl_apps(skipped, tc);
        let (out, h4) = out_unred.whnf_core(tc);
        Some(ReduceQuotLift::Base {
            c_levels,
            args,
            qmk_A_r,
            a,
            qmk_levels : qmk_const_levels,
            qmk_args,
            out_unred,
            out,
            skipped,
            qmk_const,
            qlift_const : self,
            qmk_A_r_a_unred,
            qmk_A_r_a,
            f,
            B,
            h1,
            h2,
            h3,
            h4,
        }.step(tc))
    }        

    
    // This is almost identical to reduce_quot_lift, but after extracting
    // (a : A) from quotmk_A_r_a, instead of applying it to argument # 5,
    // (f : A -> B) we're applying it to argument # 4, 
    // which is `(∀ (a : A), B (@quot.mk A r a))`
    #[has_try_some(method = "self.reduce_quot_ind(args, tc)")]
    fn reduce_quot_ind(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ReduceQuotIndZst>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;
        let (qmk_n, _, qind_n) = tc.quot_names()?;
        let (qmk_pos, B_of_pos) = if c_name == qind_n { (4, 3) } else { return None };

        
        let qmk_A_r_a_unred = args.get(qmk_pos, tc)?;
        
        let (qmk_A_r_a, h1) = qmk_A_r_a_unred.whnf(tc);

        let ((qmk_const, qmk_args), h2) = qmk_A_r_a.unfold_apps(tc);
        let (qmk_const_name, qmk_const_levels) = qmk_const.try_const_info(tc)?;
        if qmk_const_name != qmk_n {
            return None
        }

        let B_of = args.get(B_of_pos, tc)?;

        let (qmk_A_r, a) = match qmk_A_r_a.read(tc) {
            App { fun : qmk_A_r, arg : a, .. } => (qmk_A_r, a),
            _ => unreachable!("Bad quot_rec (lift) app")
        };
        
        let B_app = B_of.new_app(a, tc);

        let skipped = args.skip(qmk_pos + 1, tc);
        let (out_unred, h3) = B_app.foldl_apps(skipped, tc);
        let (out, h4) = out_unred.whnf_core(tc);

        Some(ReduceQuotInd::Base {
            c_levels,
            args,
            qmk_A_r,
            a,
            qmk_levels : qmk_const_levels,
            qmk_args,
            out_unred,
            out,
            skipped,
            qmk_const,
            qind_const : self,
            B_of,
            qmk_A_r_a_unred,
            qmk_A_r_a,
            B_app,
            h1,
            h2,
            h3,
            h4,
        }.step(tc))

    }        

    fn mk_nullary_ctor(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<MkNullaryCtorZst>)> {
        let ((fun, args), h1) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let (dptr, h_admitted) = tc.get_declar(c_name)?;
        let h2 = (c_name, h_admitted, dptr);

        let (
            zth_ctor_name, 
            d_uparams,
            d_type,
            d_num_params,
            d_all_ind_names,
            d_all_ctor_names,
            d_is_unsafe,
        ) = match dptr.read(tc) {
            Inductive { 
                uparams : d_uparams, 
                type_ : d_type,
                num_params,
                all_ind_names,
                all_ctor_names, 
                is_unsafe,
                .. 
            } => match all_ctor_names.get(0, tc) {
                None => return None,
                Some(n) => (
                    n, 
                    d_uparams,
                    d_type,
                    num_params,
                    all_ind_names,
                    all_ctor_names,
                    is_unsafe,
                )
            }
            _ => return None
        };

        let fold_const = <ExprPtr>::new_const(zth_ctor_name, c_levels, tc);
        let fold_args = args.take(d_num_params as usize, tc);
        let (out, h3) = fold_const.foldl_apps(fold_args, tc);
        Some(MkNullaryCtor::Base {
            e : self,
            c_name,
            c_levels,
            args,
            d_uparams,
            d_type,
            d_num_params,
            d_all_ind_names,
            d_all_ctor_names,
            d_is_unsafe,
            out,
            base : fun,
            zth_ctor_name,
            fold_args,
            ind : dptr,
            fold_const,
            h1,
            h2,
            h3,
        }.step(tc))
    }    

    // Either returns the altered major or returns the original major.
    fn to_ctor_when_k(
        self,
        recursor : DeclarPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<ToCtorWhenKZst>) {
        match self.try_to_ctor_when_k_aux(recursor, tc) {
            Some(r) => r,
            None => {
                ToCtorWhenK::Skip {
                    e : self,
                    d : recursor,
                }.step(tc)
            }
        }
    }

    #[has_try_some(method = "self.to_ctor_when_k_aux(recursor, tc)")]
    fn to_ctor_when_k_aux(
        self,
        recursor : DeclarPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<ToCtorWhenKZst>)> {
        ret_none_if! { !recursor.rec_is_k(tc)? };
        
        let (e_type_unred, h1) = self.infer(InferOnly, tc);
        let (e_type, h2) = e_type_unred.whnf(tc);

        
        let ((e_t_fun, c_args), h3) = e_type.unfold_apps(tc);
        let (c_name, c_levels) = match e_t_fun.read(tc) {
            Const { name, levels } if recursor.name(tc).get_prefix(tc) == name => {
                (name, levels)
            },
            _ => return None
        };

        let (ctor_app, h4) = e_type.mk_nullary_ctor(tc)?;
        let (ctor_app_type, h5) = ctor_app.infer(InferOnly, tc);
        let h6 = match e_type.try_def_eq(ctor_app_type, tc) {
            (NeShort, _) => return None,
            (EqShort, h6) => h6
        };


        Some(ToCtorWhenK::Base {
            e : self,
            d_uparams : recursor.uparams(tc),
            d_type : recursor.type_(tc),
            d_all_names : recursor.rec_all_names(tc).unwrap(),
            d_num_params : recursor.rec_num_params(tc).unwrap(),
            d_num_indices : recursor.rec_num_indices(tc).unwrap(),
            d_num_motives : recursor.rec_num_motives(tc).unwrap(),
            d_num_minors : recursor.rec_num_minors(tc).unwrap(),
            d_major_idx : recursor.rec_major_idx(tc).unwrap(),
            d_rec_rules : recursor.rec_rules(tc).unwrap(),
            d_is_k : recursor.rec_is_k(tc).unwrap(),
            d_is_unsafe : recursor.is_unsafe(tc),
            e_type_unred,
            e_type,
            c_name,
            c_levels,
            c_args,
            ctor_app,
            ctor_app_type,
            const_ : e_t_fun,
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
        }.step(tc))
    }

    
    #[has_try_some(method = "self.reduce_ind_rec(args, tc)")]
    fn reduce_ind_rec(
        self, 
        args : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> Option<(ExprPtr<'l>, Step<ReduceIndRecZst>)> {
        let (c_name, c_levels) = self.try_const_info(tc)?;

        let (recursor, h_admitted) = tc.get_declar(c_name)?;
        let h1 = (c_name, h_admitted, recursor);
        match recursor.read(tc) {
            Recursor {..} => (),
            _ => return None
        }


        ret_none_if! { recursor.rec_major_idx(tc)? as usize >= args.len(tc) };
        ret_none_if! { c_levels.len(tc) != recursor.uparams(tc).len(tc) };

        let major_unredA = args.get(recursor.rec_major_idx(tc)? as usize, tc)?;

       let (major_unredB, h2) = major_unredA.to_ctor_when_k(recursor, tc);

       let (major, h3) = major_unredB.whnf(tc);

       let ((major_fun, major_args), h4) = major.unfold_apps(tc);
       let (major_name, major_levels) = major_fun.try_const_info(tc)?;

       let (got_rec_rule, h5) = recursor.rec_rules(tc)?.get_rec_rule(major_name, tc)?;

       let major_args_len = major_args.len(tc);
       let sub_num_params = major_args_len.checked_sub(got_rec_rule.read(tc).num_fields as usize)?;


        let take_size = recursor.rec_num_params(tc)?
                      + recursor.rec_num_motives(tc)?
                      + recursor.rec_num_minors(tc)?;       
       let skip1 = major_args.skip(sub_num_params, tc);
       // end_apps
       let take1 = skip1.take(got_rec_rule.read(tc).num_fields as usize, tc);
       let skip2 = args.skip((recursor.rec_major_idx(tc)? + 1) as usize , tc);
       let take2 = args.take(take_size as usize, tc);

       let (r6, h6) = got_rec_rule.read(tc).val.subst(recursor.uparams(tc), c_levels, tc);
       let (r7, h7) = r6.foldl_apps(take2, tc);
       let (r8, h8) = r7.foldl_apps(take1, tc);
       let (r9, h9) = r8.foldl_apps(skip2, tc);
       let (r10, h10) = r9.whnf_core(tc);

       Some(ReduceIndRec::Base {
           c_name,
           c_levels,
           args,
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
           major_unredB,
           major_name,
           major_levels,
           major_args,
           major,
           rr_name : got_rec_rule.read(tc).ctor_name,
           rr_n_fields : got_rec_rule.read(tc).num_fields,
           rr_val : got_rec_rule.read(tc).val,
           major_args_len,
           r6,
           r7,
           r8,
           r9,
           r10,
           base_const : self,
           major_unredA,
           major_fun,
           got_rec_rule,
           skip1,
           skip2,
           take1,
           take2,
           recursor,
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
       }.step(tc))
    }        


    pub fn whnf_core(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<WhnfCoreZst>) {
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
            (Lambda {..}, Cons(..)) => {
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
    ) -> (ExprPtr<'l>, Step<WhnfZst>) {
        if let Some(cached) = tc.check_whnf_cache(&self) {
            cached
        } else {
            let (whnf_cored, h1) = self.whnf_core(tc);
            let result = if let Some((unfolded, h2)) = whnf_cored.try_unfold_def(tc) {
                let (e_prime, h3) = unfolded.whnf(tc);
                Whnf::Unfolding{
                    e : self,
                    cored : whnf_cored,
                    unfolded,
                    e_prime,
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
            };
            tc.insert_whnf_cache(self, result);
            result
        }
    }        

}
