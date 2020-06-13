use crate::exprs;
use crate::name::{ NamePtr, NamesPtr };
use crate::level::{ LevelPtr, Level, LevelsPtr };
use crate::expr::{ Expr, Expr::*, ExprPtr, ExprsPtr, BinderStyle::* };
use crate::env::{ Declar::*, ReducibilityHint::* };
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
                let (e_prime, h2) = self.inst(lambda_args, tc);
                let (e_prime_prime, h3) = e_prime.foldl_apps(rem_args, tc);
                WhnfLambda::NotLambda {
                    e : self,
                    rem_args,
                    lambda_args,
                    e_prime,
                    h1,
                    h2,
                    h3,
                    e_prime_prime,
                }.step(tc)
            },
            (_, Nil) => {
                let (e_prime, h1) = self.inst(lambda_args, tc);
                WhnfLambda::NoArgs {
                    e : self,
                    lambda_args,
                    e_prime,
                    h1,
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
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<WhnfLet<'l>>) {
        match self.read(tc) {
            Let { b_name, b_type, b_style, val, body, .. } => {
                let (body_prime, h1) = body.inst1(val, tc);
                WhnfLet::Base {
                    b_name,
                    b_type,
                    b_style,
                    val,
                    body,
                    body_prime,
                    h1,
                    ind_arg1 : self
                }.step(tc)
            },
            _ => unreachable!("Checked pattern match; whnf_let")
        }
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
                let (e_prime_prime, h3) = e_prime.whnf_core(tc);
                WhnfCore::Lambda {
                    e : self,
                    lam : fun,
                    args,
                    e_prime,
                    e_prime_prime,
                    h1,
                    h2,
                    h3
                }.step(tc)
            },
            (Let {..}, _) => {
                unimplemented!()
            },
            _ => unimplemented!("Rest of whnf_core not yet implemented")
        }
    }


}

