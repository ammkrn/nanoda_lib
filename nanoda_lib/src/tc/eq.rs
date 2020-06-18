use nanoda_macros::has_try;

use crate::ret_none_if;
use crate::{ name, param, arrow, sort, app };
use crate::name::{ NamePtr, NamesPtr, Name, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle, BinderStyle::* };
use crate::tc::infer::InferFlag::*;
use crate::env::{ Declar, DeclarPtr, Declar::* };
use crate::trace::IsTracer;
use crate::trace::steps::*;
use crate::utils::{ 
    Ptr,
    List::*,
    ListPtr,
    Env,
    IsCtx,
    IsTc,
    Tc,
    Pfinder,
    HasNanodaDbg 
};

use ShortCircuit::*;
use DeltaResult::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShortCircuit {
    EqShort,
    NeShort
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeltaResult<'a> {
    Short(ShortCircuit),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

// sub-functions return
// Option<EqCtorResult<DefEqPi>>
// if let Some(eq_cotr_res) = try_def_eq_pi(self, other, tc)
// match eq_ctor_res {
//   NeShort => return None
//   EqShort(ss, step) => {..}
//}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EqCtorResult<S> {
    EqShort(ShortCircuit, Step<S>),
    NeShort,
}

/*
I think there's still value to caching Neq
Maybe not
*/

#[macro_export]
macro_rules! ne_if_none {
    ( $x:expr ) => {

    };
}

#[macro_export]
macro_rules! wrap_def_eq {
    ( $ss:ident, $step:expr ) => {
        match $ss {
            NeShort => {
                assert!(<TC as IsCtx>::IS_PFINDER);
                None
            },
            EqShort => {
                Some($step)
            }
        }
    };
}

impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    /*
    Returns an option; the actual printing Tc should never
    encounter a NeShort value, since the branches it takes
    have either been cleared by a Pfinder, or are a hard error.


    I think it's fine to leave NeShort cache values in without clearing them
    between Pfinders?


    match the short cirsuit;
    if it's NeShort,
    assert you have a Pfinder,
    and then return None
    

    The "sub-methods" like DefEqPi shoudl be able to return NeShort,
    but DefEq itself should not be able to in this version, since we're
    not going to cache NeShort results.

    
    */
    #[has_try(method = "self.def_eq(other, tc)")]
    pub fn def_eq<TC : IsTc<'t, 'l, 'e>>(
        self,
        other : Self,
        tc : &mut TC,
    ) -> Option<Step<DefEq<'l>>> {
        unimplemented!()
        /*
        if self == other {
            Some(DefEq::PtrEq {
                l : self,
                r : other,
                ss : EqShort
            }.step(tc))
        } else if let Some((ss, h1)) = tc.check_eq_cache(self, other) {
            Some(DefEq::CacheHit {
                l : self,
                r : other,
                ss,
                h1,
            }.step(tc))
        } else {
            let (result, step) = {
                let (lw, h1) = self.whnf_core(tc);
                let (rw, h2) = other.whnf_core(tc);

                if let Some(x) = lw.try_def_eq_sort(rw, tc) {
                    match x {
                        NeShort => {
                            assert!(<TC as IsCtx>::IS_PFINDER);
                            None
                        }
                        (EqShort, h3) => {
                            Some(DefEq::Sort {
                                l : self,
                                r : other,
                                lw,
                                rw,
                                ss,
                                h1,
                                h2,
                                h3
                            }.step(tc))
                        }
                    }
                } else if let Some((ss, h3)) = lw.try_def_eq_pi(rw, tc) {
                    DefEq::Pi {
                        l : self,
                        r : other,
                        lw,
                        rw,
                        ss,
                        h1,
                        h2,
                        h3
                    }.step(tc)
                } else if let Some((ss, h3)) = lw.try_def_eq_lambda(rw, tc) {
                    DefEq::Lambda {
                        l : self,
                        r : other,
                        lw,
                        rw,
                        ss,
                        h1,
                        h2,
                        h3
                    }.step(tc)
                } else if let Some((ss, h3)) = lw.try_proof_irrel_eq(rw, tc) {
                    DefEq::ProofIrrelEq {
                        l : self,
                        r : other,
                        lw,
                        rw,
                        ss,
                        h1,
                        h2,
                        h3
                    }.step(tc)
                } else {
                    let (delta_result, h3) = lw.lazy_delta_step(rw, tc);
                    match delta_result {
                        Short(ss) => {
                            DefEq::DeltaShort {
                                l : self,
                                r : other,
                                lw,
                                rw,
                                ss,
                                h1,
                                h2,
                                h3
                            }.step(tc)
                        },
                        Exhausted(l_d, r_d) => {
                            if let Some((ss, h4)) = l_d.try_def_eq_const(r_d, tc) {
                                DefEq::EqConst {
                                    l : self,
                                    r : other,
                                    lw,
                                    rw,
                                    l_d,
                                    r_d,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    h4
                                }.step(tc)
                            } else if let Some((ss, h4)) = l_d.try_def_eq_local(r_d, tc) {
                                DefEq::EqLocal {
                                    l : self,
                                    r : other,
                                    lw,
                                    rw,
                                    l_d,
                                    r_d,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    h4
                                }.step(tc)
                            } else if let Some((ss, h4)) = l_d.try_def_eq_app(r_d, tc) {
                                DefEq::EqApp {
                                    l : self,
                                    r : other,
                                    lw,
                                    rw,
                                    l_d,
                                    r_d,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    h4
                                }.step(tc)
                            } else if let Some((ss, h4)) = l_d.try_def_eq_eta(r_d, tc) {
                                DefEq::EtaLr {
                                    l : self,
                                    r : other,
                                    lw,
                                    rw,
                                    l_d,
                                    r_d,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    h4
                                }.step(tc)
                            } else if let Some((ss, h4)) = r_d.try_def_eq_eta(l_d, tc) {
                                DefEq::EtaRl {
                                    l : self,
                                    r : other,
                                    lw,
                                    rw,
                                    l_d,
                                    r_d,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    h4
                                }.step(tc)
                            } else {
                                DefEq::Ne {
                                    l : self,
                                    r : other,
                                    ss : NeShort
                                }.step(tc)
                            }
                        }
                    }
                }
            };

            match result {
                None => {
                    //assert!(<TC as IsCtx>::IS_PFINDER);
                    //tc.insert_eq_cache(self, other, result, step);
                    None
                },
                Some((NeShort, _)) => {
                    unimplemented!()
                }
                Some((EqShort, step)) => {
                    tc.insert_eq_cache(self, other, result, step);
                    Some((result, step))
                }
            }
            
        }

        */
    }

    fn try_def_eq_sort(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> Option<(ShortCircuit, Step<DefEqSort<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (Sort { level : l1 }, Sort { level : l2 }) => {
                let (ssb, h1) = l1.eq_antisymm(l2, tc);
                let ss = match ssb {
                    true => EqShort,
                    false => NeShort
                };
                Some(DefEqSort::Base {
                    l1,
                    l2,
                    ss,
                    h1,
                    ind_arg1 : self,
                    ind_arg2 : other,
                }.step(tc))
            },
            _ => None
        }
    }

    // `try` is different here since this wrapper function
    // implements try-like behavior, and we want to return
    // NeShort if they're both Pis AND not equal.
    fn try_def_eq_pi(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqPi<'l>>)> {
    //) -> Option<CtorEqResult<DefEqPi<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (Pi {..}, Pi {..}) => {
                Some(self.def_eq_pi(other, Nil::<Expr>.alloc(tc), tc))
            },
            _ => None
        }
    }

    #[allow(unconditional_recursion)]
    fn def_eq_pi(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> (ShortCircuit, Step<DefEqPi<'l>>) {
    //) -> EqCtorResult {
        match (self.read(tc), other.read(tc)) {
            (
                Pi { b_name : n1, b_type : t1, b_style : s1, body : b1, .. },
                Pi { b_name : n2, b_type : t2, b_style : s2, body : b2, .. }
            ) => {
                let (t1_prime, h1) = t1.inst(doms, tc);
                let (t2_prime, h2) = t2.inst(doms, tc);
                let (ss_binders, h3) = t1_prime.def_eq(t2_prime, tc);
                /*
                let h3 = match t1_prime.def_eq(t2_prime, tc) {
                    None => return EqCtorResult::NeShort,
                    Some(h3) => h3
                };
                */
                if let NeShort = ss_binders {
                    DefEqPi::StepNe {
                        lbn : n1,
                        lbt : t1,
                        lbs : s1,
                        lbo : b1,
                        rbn : n2,
                        rbt : t2,
                        rbs : s2,
                        rbo : b2,
                        lbt_prime : t1_prime,
                        rbt_prime : t2_prime,
                        doms,
                        ss : ss_binders,
                        h1,
                        h2,
                        h3,
                        ind_arg1 : self,
                        ind_arg2 : other,
                    }.step(tc)
                } else {
                    let local = <ExprPtr>::new_local(n1, t1_prime, s1, tc);
                    let (ss_bodies, h4) = b1.def_eq_pi(b2, Cons(local, doms).alloc(tc), tc);
                    DefEqPi::StepEq {
                        lbn : n1,
                        lbt : t1,
                        lbs : s1,
                        lbo : b1,
                        rbn : n2,
                        rbt : t2,
                        rbs : s2,
                        rbo : b2,
                        lbt_prime : t1_prime,
                        rbt_prime : t2_prime,
                        doms,
                        ss : ss_binders,
                        h1,
                        h2,
                        h3,
                        h4,
                        ind_arg1 : self,
                        ind_arg2 : other,
                    }.step(tc)
                }
            },
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                let (ss, h3) = l_prime.def_eq(r_prime, tc);
                DefEqPi::Base {
                    l : self,
                    r : other,
                    l_prime,
                    r_prime,
                    doms,
                    ss,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }

    
    // `try` is different here since this wrapper function
    // implements try-like behavior, and we want to return
    // NeShort if they're both lambdas AND they're not equal.
    fn try_def_eq_lambda(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqLambda<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (Lambda {..}, Lambda {..}) => {
                Some(self.def_eq_lambda(other, Nil::<Expr>.alloc(tc), tc))
            },
            _ => None
        }
    }

    #[allow(unconditional_recursion)]
    fn def_eq_lambda(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> (ShortCircuit, Step<DefEqLambda<'l>>) {
        match (self.read(tc), other.read(tc)) {
            (
                Lambda { b_name : n1, b_type : t1, b_style : s1, body : b1, .. },
                Lambda { b_name : n2, b_type : t2, b_style : s2, body : b2, .. }
            ) => {
                let (t1_prime, h1) = t1.inst(doms, tc);
                let (t2_prime, h2) = t2.inst(doms, tc);
                let (ss_binders, h3) = t1_prime.def_eq(t2_prime, tc);
                let h3 = neq_if_none! { tl_prime.def_eq(t2_prime, tc) };
                //let h3 = match tl_prime.def_eq(t2_prime, tc) {
                //    Some(h3) => h3,
                //    None => return NeShort
                //}
                if let NeShort = ss_binders {
                    unimplemented!()
                   // DefEqLambda::StepNe {
                   //     lbn : n1,
                   //     lbt : t1,
                   //     lbs : s1,
                   //     lbo : b1,
                   //     rbn : n2,
                   //     rbt : t2,
                   //     rbs : s2,
                   //     rbo : b2,
                   //     lbt_prime : t1_prime,
                   //     rbt_prime : t2_prime,
                   //     doms,
                   //     ss : ss_binders,
                   //     h1,
                   //     h2,
                   //     h3,
                   //     ind_arg1 : self,
                   //     ind_arg2 : other,
                   // }.step(tc)
                } else {
                    let local = <ExprPtr>::new_local(n1, t1_prime, s1, tc);
                    let (ss_bodies, h4) = b1.def_eq_pi(b2, Cons(local, doms).alloc(tc), tc);
                    DefEqLambda::StepEq {
                        lbn : n1,
                        lbt : t1,
                        lbs : s1,
                        lbo : b1,
                        rbn : n2,
                        rbt : t2,
                        rbs : s2,
                        rbo : b2,
                        lbt_prime : t1_prime,
                        rbt_prime : t2_prime,
                        doms,
                        ss : ss_binders,
                        h1,
                        h2,
                        h3,
                        h4,
                        ind_arg1 : self,
                        ind_arg2 : other,
                    }.step(tc)
                }
            },
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                let (ss, h3) = l_prime.def_eq(r_prime, tc);
                DefEqLambda::Base {
                    l : self,
                    r : other,
                    l_prime,
                    r_prime,
                    doms,
                    ss,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }    

    fn try_def_eq_const(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqConst<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (
                Const { name : l_name, levels : l_levels }, 
                Const { name : r_name, levels : r_levels }
            ) if l_name == r_name => {
                let (levels_eq, h1) = l_levels.eq_antisymm_many(r_levels, tc);
                match (l_name == r_name && levels_eq) {
                    false => None,
                    true => {
                        Some(DefEqConst::Base {
                            l_name,
                            r_name,
                            l_levels,
                            r_levels,
                            ss : EqShort,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : other,
                        }.step(tc))
                    }
                }
            },
            _ => None
        }
    }

    fn try_def_eq_local(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqLocal<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (
                Local { b_name : lbn, b_type : lbt, b_style : lbs, serial : l_serial }, 
                Local { b_name : rbn, b_type : rbt, b_style : rbs, serial : r_serial }
            ) if l_serial == r_serial => {
                Some(DefEqLocal::Base {
                    lbn,
                    rbn,
                    lbt,
                    rbt,
                    lbs,
                    rbs,
                    l_serial,
                    r_serial,
                    ss : EqShort,
                    ind_arg1 : self,
                    ind_arg2 : other,
                }.step(tc))
            },
            _ => None
        }
    }    

    fn try_def_eq_app(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqApp<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (App {..}, App {..}) => {
                let ((l_fun, l_args), h1) = self.unfold_apps(tc);
                let ((r_fun, r_args), h2) = other.unfold_apps(tc);
                let (funs_ss, h3) = l_fun.def_eq(r_fun, tc);
                match funs_ss {
                    NeShort => None,
                    EqShort => {
                        let (ss, h4) = args_eq(l_args, r_args, tc);
                        match ss {
                            NeShort => None,
                            EqShort => {
                                Some(DefEqApp::Base {
                                    l_fun,
                                    r_fun,
                                    l_args,
                                    r_args,
                                    funs_ss,
                                    ss : EqShort,
                                    h1,
                                    h2,
                                    h3,
                                    h4,
                                    ind_arg1 : self,
                                    ind_arg2 : other,
                                }.step(tc))
                            }
                        }
                    }
                }
            },
            _ => None
        }
    }        

    fn try_def_eq_eta(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<DefEqEta<'l>>)> {
        match (self.read(tc), other.read(tc)) {
            (_, Lambda {..}) => None,
            (Lambda { b_name : lbn, b_type : lbt, b_style : lbs, body : lbo, .. }, _) => {
                let (other_type_unred, h1) = other.infer(InferOnly, tc);
                let (other_type, h2) = other_type_unred.whnf(tc);
                match other_type.read(tc) {
                    Pi { b_name : rbn, b_type : rbt, b_style : rbs, body : rbo, .. } => {
                        let new_body = other.new_app(<ExprPtr>::new_var(0, tc), tc);
                        let new_lambda = <ExprPtr>::new_lambda(rbn, rbt, rbs, new_body, tc);
                        let (ss, h3) = self.def_eq(new_lambda, tc);
                        match ss {
                            NeShort => None,
                            EqShort => {
                                Some(DefEqEta::Base {
                                    r : other,
                                    lbn,
                                    rbn,
                                    lbt,
                                    rbt,
                                    lbs,
                                    rbs,
                                    lbo,
                                    rbo,
                                    ss,
                                    h1,
                                    h2,
                                    h3,
                                    ind_arg1 : self,

                                }.step(tc))
                            }
                        }
                    },
                    _ => None
                }
            }
            _ => None
        }
    }

    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_sort_zero(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(bool, Step<IsSortZero<'l>>)> {
        let (whnfd, h1) = self.whnf(tc);
        match whnfd.read(tc) {
            Sort { level } if level.is_zero_lit(tc).0 => {
                Some(IsSortZero::Base {
                    e : self,
                    b : true,
                    h1,
                }.step(tc))
            },
            _ => None
        }
    }

    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_proposition(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<IsProposition<'l>>)> {
        let (infd, h1) = self.infer(InferOnly, tc);
        let (is_zero, h2) = infd.is_sort_zero(tc)?;
        assert!(is_zero);
        Some(IsProposition::Base {
            e : self,
            infd,
            h1,
            h2,
        }.step(tc))
    }

    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_proof(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<IsProof<'l>>)> {
        let (infd, h1) = self.infer(InferOnly, tc);
        let (_maybe_sort_zero, h2) = infd.is_proposition(tc)?;
        Some(IsProof::Base {
            e : self,
            infd,
            h1,
            h2,
        }.step(tc))

    }

    #[has_try(method = "self.proof_irrel_eq(other, tc)")]
    fn proof_irrel_eq(
        self : ExprPtr<'l>,
        other : ExprPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ShortCircuit, Step<ProofIrrelEq<'l>>)> {
        let (l_type, h1) = self.is_proof(tc)?;
        let (r_type, h2) = other.is_proof(tc)?;
        let (ss, h3) = l_type.def_eq(r_type, tc);
        if let EqShort = ss {
            Some(ProofIrrelEq::Base {
                l : self,
                r : other,
                l_type,
                r_type,
                ss,
                h1,
                h2,
                h3,
            }.step(tc))
        } else {
            None
        }
    }
    
    pub fn delta_check(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (DeltaResult<'l>, Step<DeltaCheck<'l>>) {
        if let Some((ss, h1)) = self.try_def_eq_sort(other, tc) {
            DeltaCheck::Sort {
                l : self,
                r : other,
                result : Short(ss),
                h1
            }.step(tc)
        } else if let Some((ss, h1)) = self.try_def_eq_pi(other, tc) {
            DeltaCheck::Pi {
                l : self,
                r : other,
                result : Short(ss),
                h1
            }.step(tc)
        } else if let Some((ss, h1)) = self.try_def_eq_lambda(other, tc) {
            DeltaCheck::Lambda {
                l : self,
                r : other,
                result : Short(ss),
                h1
            }.step(tc)
        } else {
            let (result, h1) = self.lazy_delta_step(other, tc);
            DeltaCheck::Step {
                l : self,
                r : other,
                result,
                h1
            }.step(tc)
        }
    }

    
    pub fn lazy_delta_step(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (DeltaResult<'l>, Step<LazyDeltaStep<'l>>) {
        let maybe_l_delta = self.try_is_delta(tc);
        let maybe_r_delta = other.try_is_delta(tc);

        match (maybe_l_delta, maybe_r_delta) {
            (None, None) => {
                LazyDeltaStep::NoneNone {
                    l : self,
                    r : other,
                    result : Exhausted(self, other)
                }.step(tc)
            },
            (Some((l_def, h1)), None) => {
                let (l_defval_unred, h2) = self.unfold_def(tc).expect("lazy_delta1");
                let (l_defval, h3) = l_defval_unred.whnf_core(tc);
                let (result, h4) = l_defval.delta_check(other, tc);
                LazyDeltaStep::SomeNone {
                    l : self,
                    r : other,
                    l_def,
                    l_defval_unred,
                    l_defval,
                    result,
                    h1,
                    h2,
                    h3,
                    h4
                }.step(tc)
            },
            (None, Some((r_def, h1))) => {
                let (r_defval_unred, h2) = other.unfold_def(tc).expect("lazy_delta2");
                let (r_defval, h3) = r_defval_unred.whnf_core(tc);
                let (result, h4) = self.delta_check(r_defval, tc);
                LazyDeltaStep::NoneSome {
                    l : self,
                    r : other,
                    r_def,
                    r_defval_unred,
                    r_defval,
                    result,
                    h1,
                    h2,
                    h3,
                    h4
                }.step(tc)
            },
            (Some((l_def, h1)), Some((r_def, h2))) 
            if l_def.get_hint(tc) < r_def.get_hint(tc) => {
                let l_hint = l_def.get_hint(tc);
                let r_hint = r_def.get_hint(tc);
                let (r_defval_unred, h3) = other.unfold_def(tc).expect("lazy_delta3");
                let (r_defval, h4) = r_defval_unred.whnf_core(tc);
                let (result, h5) = self.delta_check(r_defval, tc);
                LazyDeltaStep::Lt {
                    l : self,
                    r : other,
                    l_def,
                    r_def,
                    l_hint,
                    r_hint,
                    r_defval_unred,
                    r_defval,
                    result,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5
                }.step(tc)                
            },
            (Some((l_def, h1)), Some((r_def, h2))) 
            if l_def.get_hint(tc) > r_def.get_hint(tc) => {
                let l_hint = l_def.get_hint(tc);
                let r_hint = r_def.get_hint(tc);
                let (l_defval_unred, h3) = self.unfold_def(tc).expect("lazy_delta4");
                let (l_defval, h4) = l_defval_unred.whnf_core(tc);
                let (result, h5) = l_defval.delta_check(other, tc);
                LazyDeltaStep::Gt {
                    l : self,
                    r : other,
                    l_def,
                    r_def,
                    l_hint,
                    r_hint,
                    l_defval_unred,
                    l_defval,
                    result,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5
                }.step(tc)                
            },
            (Some((l_def, h1)), Some((r_def, h2))) => {
                assert_eq!(l_def.get_hint(tc), r_def.get_hint(tc));
                if let (App {..}, App {..}) = (self.read(tc), other.read(tc)) {
                    if l_def == r_def {
                        let ((l_fun, l_args), h1) = self.unfold_apps(tc);
                        let ((r_fun, r_args), h2) = other.unfold_apps(tc);
                        if let (
                            Some((lc_name, lc_levels)), 
                            Some((rc_name, rc_levels))
                         ) = (l_fun.try_const_info(tc), r_fun.try_const_info(tc)) {
                            let (args_eq, h3) = args_eq(l_args, r_args, tc);
                            if let EqShort = args_eq {
                                let (levels_eq, h4) = lc_levels.eq_antisymm_many(rc_levels, tc);
                                if levels_eq {
                                    // This is the only explicit/short-circuiting
                                    // return. It avoids a shit-ton of noise so I'm going to let
                                    // it rock, but just making a note 
                                    return LazyDeltaStep::EqShort {
                                        l : self,
                                        r : other,
                                        l_def,
                                        r_def,
                                        result : Short(EqShort),
                                        h1,
                                        h2,
                                        h3,
                                        h4
                                    }.step(tc)
                                }
                            }
                        }
                    }
                }
        
                let (l_defval_unred, h1) = self.unfold_def(tc).expect("heights_eq 1");
                let (r_defval_unred, h2) = other.unfold_def(tc).expect("heights_eq 2");
                let (l_defval, h3) = l_defval_unred.whnf_core(tc);
                let (r_defval, h4) = r_defval_unred.whnf_core(tc);
                let (result, h5) = l_defval.delta_check(r_defval, tc);
                LazyDeltaStep::Owise {
                    l : self,
                    r : other,
                    l_def,
                    r_def,
                    l_defval_unred,
                    r_defval_unred,
                    l_defval,
                    r_defval,
                    result,
                    h1,
                    h2,
                    h3,
                    h4,
                    h5,
                }.step(tc)
            },
        }
    }

   // I think in the `None` case you don't want to bother returning anything,
   // since the assertion is only that in the positive case, there's 
   // some definition to unfold to.
    #[has_try(method = "self.is_delta(tc)")]
    pub fn is_delta(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(DeclarPtr<'l>, Step<IsDelta<'l>>)> {
        let ((fun, args), h1) = self.unfold_apps(tc);
        let (c_name, c_levels) = fun.try_const_info(tc)?;
        let (d, h2) = tc.get_declar(c_name)?;
        match d.read(tc) {
            Definition { name, uparams, type_, val, hint, is_unsafe } => {
                Some(IsDelta::Base {
                    e : self,
                    c_name,
                    c_levels,
                    args,
                    name,
                    uparams,
                    type_,
                    val,
                    hint,
                    is_unsafe,
                    h1,
                    h2,
                    ind_arg2 : d,
                }.step(tc))
            },
            _ => None
        }
    }    

}


// I don't think you need a `try` function for this since it's only
// ever called from other functios that are already wrapped in `try`
// such that control-flow can only short-circuit because of this.
pub fn args_eq<'t, 'l : 't, 'e : 'l>(
    ls : ExprsPtr<'l>, 
    rs : ExprsPtr<'l>, 
    tc : &mut impl IsTc<'t, 'l, 'e>
) -> (ShortCircuit, Step<ArgsEq<'l>>) {
    let (ls_len, h1) = ls.len(tc);
    let (rs_len, h2) = rs.len(tc);
    if ls_len == rs_len {
        let (aux_result, h3) = args_eq_aux(ls, rs, tc);
        ArgsEq::Step {
            ls,
            rs,
            ls_len,
            rs_len,
            ss : aux_result,
            h1,
            h2,
            h3,
        }.step(tc)
    } else {
        ArgsEq::Base {
            ls,
            rs,
            ls_len,
            rs_len,
            ss : NeShort,
            h1,
            h2,
        }.step(tc)
    }

}

pub fn args_eq_aux<'t, 'l : 't, 'e : 'l>(
    ls : ExprsPtr<'l>, 
    rs : ExprsPtr<'l>, 
    tc : &mut impl IsTc<'t, 'l, 'e>
) -> (ShortCircuit, Step<ArgsEqAux<'l>>) {
    match (ls.read(tc), rs.read(tc)) {
        (Nil, Nil) => {
            ArgsEqAux::BaseNil {
                ss : EqShort,
                ind_arg1 : ls,
                ind_arg2 : rs,
            }.step(tc)
        },
        (Cons(x, xs), Cons(y, ys)) => {
            let (hds_eq, h1) = x.def_eq(y, tc);
            match hds_eq {
                NeShort => {
                    ArgsEqAux::BaseHdsNe {
                        l : x,
                        r : y,
                        ls_tl : xs,
                        rs_tl : ys,
                        ss : NeShort,
                        h1,
                        ind_arg1 : ls,
                        ind_arg2 : rs,
                    }.step(tc)
                },
                EqShort => {
                    let (tls_eq, h2) = args_eq_aux(xs, ys, tc);
                    ArgsEqAux::StepHdsEq {
                        l : x,
                        r : y,
                        ls_tl : xs,
                        rs_tl : ys,
                        ss : tls_eq,
                        h1,
                        h2,
                        ind_arg1 : ls,
                        ind_arg2 : rs,
                    }.step(tc)
                }
            }
        },
        _ => unreachable!(
            "Unchecked and unequal list lengths in args_eq_aux; \
            should always be checked by `args_eq`"
        )
    }
}
