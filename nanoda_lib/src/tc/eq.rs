use nanoda_macros::{ has_try_eq, has_try_some };
use crate::level::Level;
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::* };
use crate::tc::infer::InferFlag::*;
use crate::env::{ DeclarPtr, ReducibilityHint };
use crate::trace::steps::*;
use crate::utils::{ 
    List::*,
    IsTc,
    //HasNanodaDbg 
};

use EqResult::*;
use DeltaResult::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EqResult {
    EqShort,
    NeShort,
}

#[derive(Debug, Clone, Copy)]
pub enum DeltaResult<'a> {
    Short(EqResult),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {

    // This shouldn't be traced at all, but it calls
    // functions that should be, so it has "try".
    #[has_try_some(method = "self.is_delta(tc)")]
    pub fn is_delta(self, tc : &mut impl IsTc<'t, 'l, 'e>) -> Option<(DeclarPtr<'l>, ReducibilityHint)> {
        let ((fun, _), _) = self.unfold_apps(tc);
        let (c_name, _) = fun.try_const_info(tc)?;
        let (d, _) = tc.get_declar(c_name)?;
        match d.get_hint(tc) {
            None => None,
            Some(hint) => Some((d, hint))
        }
    }

    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_sort_zero(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<Step<IsSortZeroZst>> {
        let (whnfd, h1) = self.whnf(tc);
        match whnfd.read(tc) {
            Sort { level } if Level::Zero == level.read(tc) => {
                Some(IsSortZero::Base {
                    e : self,
                    z : whnfd,
                    h1,
                }.step_only(tc))
            },
            _ => None
        }
    }

    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_proposition(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(ExprPtr<'l>, Step<IsPropositionZst>)> {
        let (infd, h1) = self.infer(InferOnly, tc);
        let h2 = infd.is_sort_zero(tc)?;
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
    ) -> Option<(ExprPtr<'l>, Step<IsProofZst>)> {
        let (infd, h1) = self.infer(InferOnly, tc);
        let (_infd_sort, h2) = infd.is_proposition(tc)?;
        Some(IsProof::Base {
            e : self,
            infd,
            h1,
            h2,
        }.step(tc))
    }    

    #[has_try_some(method = "self.proof_irrel_eq(other, tc)")]
    fn proof_irrel_eq(
        self : ExprPtr<'l>,
        other : ExprPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(EqResult, Step<ProofIrrelEqZst>)> {
        let (l_type, h1) = self.is_proof(tc)?;
        let (r_type, h2) = other.is_proof(tc)?;
        match l_type.try_def_eq(r_type, tc) {
            (NeShort, _) => None,
            (EqShort, h3) => {
                Some(ProofIrrelEq::Base {
                    l : self,
                    r : other,
                    l_type,
                    r_type,
                    result : EqShort,
                    h1,
                    h2,
                    h3
                }.step(tc))
            }
        }
    }    


    pub fn assert_def_eq(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Step<DefEqZst> {
        match self.try_def_eq(other, tc) {
            (NeShort, _) => panic!("bad def eq"),
            (EqShort, h) => h,
        }
    }

    #[has_try_eq(method = "self.def_eq(other, tc)")]
    pub fn def_eq<TC : IsTc<'t, 'l, 'e>>(
        self,
        other : Self,
        tc : &mut TC,
    ) -> (EqResult, Step<DefEqZst>) {
        if self == other {
            DefEq::PtrEq {
                l : self,
                r : other,
                result : EqShort,
            }.step(tc)
        } else if let Some(cached) = tc.check_eq_cache(self, other) {
            cached
        } else {
            let result = self.def_eq_core(other, tc);
            tc.insert_eq_cache(self, other, result);
            result
        } 
    }

    fn def_eq_core<TC : IsTc<'t, 'l, 'e>>(
        self,
        other : Self,
        tc : &mut TC,
    ) -> (EqResult, Step<DefEqZst>) {
        let (l_w, h1) = self.whnf_core(tc);
        let (r_w, h2) = other.whnf_core(tc);

        let result = 
        match (l_w.read(tc), r_w.read(tc)) {
            (Sort {..}, Sort {..}) => {
                let (result, h3) = l_w.def_eq_sort(r_w, tc);
                DefEq::Sort {
                    l : self,
                    r : other,
                    l_w,
                    r_w,
                    result,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
            (Pi {..}, Pi {..}) => {
                let (result, h3) = l_w.def_eq_pi(r_w, Nil::<Expr>.alloc(tc), tc);
                DefEq::Pi {
                    l : self,
                    r : other,
                    l_w,
                    r_w,
                    result,
                    h1,
                    h2,
                    h3
                }.step(tc)
            },
            (Lambda {..}, Lambda {..}) => {
                let (result, h3) = l_w.def_eq_lambda(r_w, Nil::<Expr>.alloc(tc), tc);
                DefEq::Lambda {
                    l : self,
                    r : other,
                    l_w,
                    r_w,
                    result,
                    h1,
                    h2,
                    h3
                }.step(tc)
            },

            _ => {

                if let Some((ss, h3)) = l_w.try_proof_irrel_eq(r_w, tc) {
                    let (result, step) = DefEq::ProofIrrelEq {
                        l : self,
                        r : other,
                        l_w,
                        r_w,
                        result : ss,
                        h1,
                        h2,
                        h3
                    }.step(tc);
                    tc.insert_eq_cache(self, other, (result, step));
                    return (result, step)

                }

                let (delta_result, h3) = l_w.lazy_delta_step(r_w, tc);
                

                match delta_result {
                    Short(result) => {

                        DefEq::DeltaShort {
                            l :self,
                            r : other,
                            l_w,
                            r_w,
                            result,
                            h1,
                            h2,
                            h3,
                        }.step(tc)
                    },
                    Exhausted(l_d, r_d) => match (l_d.read(tc), r_d.read(tc)) {
                        

                        (Const {..}, Const {..}) => {


                            let (result, h4) = l_d.def_eq_const(r_d, tc);
                            DefEq::Const {
                                l : self,
                                r : other,
                                l_w,
                                r_w,
                                l_d,
                                r_d,
                                result,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        },
                        (Local {..}, Local {..}) => {

                        let (result, h4) = l_d.def_eq_local(r_d, tc);
                            DefEq::Local {
                                l : self,
                                r : other,
                                l_w,
                                r_w,
                                l_d,
                                r_d,
                                result,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        },
                        (App {..}, App {..}) => {
                            let (result, h4) = l_d.def_eq_app(r_d, tc);
                            DefEq::App {
                                l : self,
                                r : other,
                                l_w,
                                r_w,
                                l_d,
                                r_d,
                                result,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        },
                        (Lambda {..}, _) => {
                            let (result, h4) = l_d.def_eq_eta(r_d, tc);
                            DefEq::EtaLr {
                                l : self,
                                r : other,
                                l_w,
                                r_w,
                                l_d,
                                r_d,
                                result,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        },
                        (_, Lambda {..}) => {
                            let (result, h4) = r_d.def_eq_eta(l_d, tc);
                            DefEq::EtaRl {
                                l : self,
                                r : other,
                                l_w,
                                r_w,
                                l_d,
                                r_d,
                                result,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        }
                        _ => {
                            (NeShort, Step::new_pfind(tc))
                        }
                    }
                }
            }
        };

        tc.insert_eq_cache(self, other, result);
        result
    }

    fn def_eq_sort(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (EqResult, Step<DefEqSortZst>) {
        match (self.read(tc), other.read(tc)) {
            (Sort { level : l1 }, Sort { level : l2 }) => {
                let (ls_eq, h1) = l1.try_eq_antisymm(l2, tc);
                match ls_eq {
                    false => (NeShort, Step::new_pfind(tc)),
                    true => DefEqSort::Base {
                            l1,
                            l2,
                            e1 : self,
                            e2 : other,
                            result : EqShort,
                            h1,
                        }.step(tc),
                }
            },
            _ => unreachable!("Checked pattern match @ def_eq_sort")
        }
    }

    #[allow(unconditional_recursion)]
    fn def_eq_pi(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> (EqResult, Step<DefEqPiZst>) {
        match (self.read(tc), other.read(tc)) {
            (
                Pi { b_name : ln, b_type : lt, b_style : ls, body : lb, .. },
                Pi { b_name : rn, b_type : rt, b_style : rs, body : rb, .. }
            ) => {
                let (lt_prime, h1) = lt.inst(doms, tc);
                let (rt_prime, h2) = rt.inst(doms, tc);
                match lt_prime.try_def_eq(rt_prime, tc) {
                    (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                    (EqShort, h3) => {
                        let local = <ExprPtr>::new_local(ln, lt_prime, ls, tc);
                        let doms_prime = Cons(local, doms).alloc(tc);
                        let (result, h4) = lb.def_eq_pi(rb, doms_prime, tc);
                        DefEqPi::Step {
                            ln,
                            rn,
                            lt,
                            rt,
                            ls,
                            rs,
                            lb,
                            rb,
                            lt_prime,
                            rt_prime,
                            doms,
                            serial : local.local_serial_infal(tc),
                            local,
                            doms_prime,
                            e1 : self,
                            e2 : other,
                            result,
                            h1,
                            h2,
                            h3,
                            h4,
                        }.step(tc)
                    }
                }
            },
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                let  (result, h3) = l_prime.try_def_eq(r_prime, tc);
                DefEqPi::Base {
                    l : self,
                    r : other,
                    doms,
                    l_prime,
                    r_prime,
                    result,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }

    #[allow(unconditional_recursion)]
    fn def_eq_lambda(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> (EqResult, Step<DefEqLambdaZst>) {
        match (self.read(tc), other.read(tc)) {
            (
                Lambda { b_name : ln, b_type : lt, b_style : ls, body : lb, .. },
                Lambda { b_name : rn, b_type : rt, b_style : rs, body : rb, .. }
            ) => {
                let (lt_prime, h1) = lt.inst(doms, tc);
                let (rt_prime, h2) = rt.inst(doms, tc);
                match lt_prime.try_def_eq(rt_prime, tc) {
                    (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                    (EqShort, h3) => {
                        let local = <ExprPtr>::new_local(ln, lt_prime, ls, tc);
                        let doms_prime = Cons(local, doms).alloc(tc);
                        let (result, h4) = lb.def_eq_lambda(rb, doms_prime, tc);
                        DefEqLambda::Step {
                            ln,
                            rn,
                            lt,
                            rt,
                            ls,
                            rs,
                            lb,
                            rb,
                            lt_prime,
                            rt_prime,
                            doms,
                            serial : local.local_serial_infal(tc),
                            local,
                            doms_prime,
                            e1 : self,
                            e2 : other,
                            result,
                            h1,
                            h2,
                            h3,
                            h4,
                        }.step(tc)
                    }
                }
            },
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                let  (result, h3) = l_prime.try_def_eq(r_prime, tc);
                DefEqLambda::Base {
                    l : self,
                    r : other,
                    doms,
                    l_prime,
                    r_prime,
                    result,
                    h1,
                    h2,
                    h3
                }.step(tc)
            }
        }
    }

    pub fn lazy_delta_recurse(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (DeltaResult<'l>, Step<LazyDeltaStepZst>) {

        match (self.read(tc), other.read(tc)) {
            (..) if self == other => {
                LazyDeltaStep::Refl {
                    l : self,
                    r : other,
                    result : Short(EqShort),
                }.step(tc)
                
            }
            (Sort {..}, Sort {..}) => {
                let (result, h1) = self.def_eq_sort(other, tc);
                LazyDeltaStep::Sort {
                    l : self,
                    r : other,
                    result : Short(result),
                    h1,
                }.step(tc)
            },
            (Pi {..}, Pi {..}) => {
                let (result, h1) = self.def_eq_pi(other, Nil::<Expr>.alloc(tc), tc);
                LazyDeltaStep::Pi {
                    l : self,
                    r : other,
                    result : Short(result),
                    h1,
                }.step(tc)
            },
            (Lambda {..}, Lambda {..}) => {
                let (result, h1) = self.def_eq_lambda(other, Nil::<Expr>.alloc(tc), tc);
                LazyDeltaStep::Lambda {
                    l : self,
                    r : other,
                    result : Short(result),
                    h1,
                }.step(tc)
            },
            _ => self.lazy_delta_step(other, tc)
        }
    }
            
    pub fn lazy_delta_step<CTX : IsTc<'t, 'l, 'e>>(
        self : Self,
        other : Self,
        tc : &mut CTX
    ) -> (DeltaResult<'l>, Step<LazyDeltaStepZst>) {
        let maybe_l_hint = self.try_is_delta(tc);
        let maybe_r_hint = other.try_is_delta(tc);
        match (maybe_l_hint, maybe_r_hint) {
            (None, None) => {
                let result = Exhausted(self, other);
                LazyDeltaStep::NoneNone {
                    l : self,
                    r : other,
                    result,
                }.step(tc)
            },
            (Some((_, _l_hint)), None) => {
                let (l_defval_unred, h1) = self.try_unfold_def(tc).expect("lazy_delta1");
                let (l_defval, h2) = l_defval_unred.whnf_core(tc);
                let (result, h3) = l_defval.lazy_delta_recurse(other, tc);
                LazyDeltaStep::UnfoldingLeft {
                    l : self,
                    r : other,
                    l_defval_unred,
                    l_defval,
                    result,
                    h1,
                    h2,
                    h3,
                }.step(tc)
            },
            (None, Some((_, _r_hint))) => {
                let (r_defval_unred, h1) = other.try_unfold_def(tc).expect("lazy_delta2");
                let (r_defval, h2) = r_defval_unred.whnf_core(tc);
                let (result, h3) = self.lazy_delta_recurse(r_defval, tc);
                LazyDeltaStep::UnfoldingRight {
                    l : self,
                    r : other,
                    r_defval_unred,
                    r_defval,
                    result,
                    h1,
                    h2,
                    h3,
                }.step(tc)
            },
            (Some((_, l_hint)), Some((_, r_hint))) if l_hint < r_hint => {
                let (r_defval_unred, h1) = other.try_unfold_def(tc).expect("lazy_delta3");
                let (r_defval, h2) = r_defval_unred.whnf_core(tc);
                let (result, h3) = self.lazy_delta_recurse(r_defval, tc);
                LazyDeltaStep::UnfoldingRight {
                    l : self,
                    r : other,
                    r_defval_unred,
                    r_defval,
                    result,
                    h1,
                    h2,
                    h3,
                }.step(tc)
            }
            (Some((_, l_hint)), Some((_, r_hint))) if r_hint < l_hint => {
                let (l_defval_unred, h1) = self.try_unfold_def(tc).expect("lazy_delta4");
                let (l_defval, h2) = l_defval_unred.whnf_core(tc);
                let (result, h3) = l_defval.lazy_delta_recurse(other, tc);
                LazyDeltaStep::UnfoldingLeft {
                    l : self,
                    r : other,
                    l_defval_unred,
                    l_defval,
                    result,
                    h1,
                    h2,
                    h3,
                }.step(tc)
            },
            (Some((l_declar, l_hint)), Some((r_declar, r_hint))) => {
                assert_eq!(l_hint, r_hint);
                if let Some(result) = self.try_delta_ext(other, l_declar, r_declar, tc) {
                    result
                } else {
                    self.delta_owise(other, tc)
                }
            }
        }
    }    

    #[has_try_some(method = "self.delta_ext(other, l_declar, r_declar, tc)")]
    fn delta_ext(
        self,
        other : Self,
        l_declar : DeclarPtr<'l>,
        r_declar : DeclarPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(DeltaResult<'l>, Step<LazyDeltaStepZst>)> {
        if let (App {..}, App {..}) = (self.read(tc), other.read(tc)) {
            if l_declar == r_declar {
                let ((l_fun, l_args), h1) = self.unfold_apps(tc);
                let ((r_fun, r_args), h2) = other.unfold_apps(tc);
                if let (
                    Some((lc_name, lc_levels)), 
                    Some((rc_name, rc_levels))
                 ) = (l_fun.try_const_info(tc), r_fun.try_const_info(tc)) {
                     if let (EqShort, h3) = try_args_eq(l_args, r_args, tc) {
                        if let (true, h4) = lc_levels.try_eq_antisymm_many(rc_levels, tc) {
                            assert_eq!(lc_name, rc_name);
                            return Some(LazyDeltaStep::Extensional {
                                 l : self,
                                 r : other,
                                 c_name : lc_name,
                                 lc_levels,
                                 rc_levels,
                                 l_const : l_fun,
                                 r_const : r_fun,
                                 l_args,
                                 r_args,
                                 result : Short(EqShort),
                                 h1,
                                 h2,
                                 h3,
                                 h4,
                            }.step(tc))
                        }
                    }
                }
            }
        }       

        None
    }

    fn delta_owise(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (DeltaResult<'l>, Step<LazyDeltaStepZst>) {
        let (l_defval_unred, h1) = self.try_unfold_def(tc).expect("heights_eq 1");
        let (r_defval_unred, h2) = other.try_unfold_def(tc).expect("heights_eq 2");
        let (l_defval, h3) = l_defval_unred.whnf_core(tc);
        let (r_defval, h4) = r_defval_unred.whnf_core(tc);
        let (result, h5) = l_defval.lazy_delta_recurse(r_defval, tc);
        LazyDeltaStep::UnfoldingBoth {
            l : self,
            r : other,
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
    }

    fn def_eq_const(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (EqResult, Step<DefEqConstZst>) {
        match (self.read(tc), other.read(tc)) {
            (
                Const { name : l_name, levels : l_levels }, 
                Const { name : r_name, levels : r_levels }
            ) if l_name == r_name => {
                match l_levels.try_eq_antisymm_many(r_levels, tc) {
                    (false, _) => (NeShort, Step::new_pfind(tc)),
                    (true, h1) => {
                        DefEqConst::Base {
                            l_name,
                            r_name,
                            l_levels,
                            r_levels,
                            e1 : self,
                            e2 : other,
                            result : EqShort,
                            h1,
                        }.step(tc)
                    }
                }
            },
            (Const {..}, Const {..}) => (NeShort, Step::new_pfind(tc)),
            _ => unreachable!("Checked pattern match @ def_eq_const")
        }
    }

    fn def_eq_local(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (EqResult, Step<DefEqLocalZst>) {
        match (self.read(tc), other.read(tc)) {
            (
                Local { b_name : ln, b_type : lt, b_style : ls, serial : l_serial }, 
                Local { b_name : rn, b_type : rt, b_style : rs, serial : r_serial }
            ) if l_serial == r_serial => {
                DefEqLocal::Base {
                    ln,
                    rn,
                    lt,
                    rt,
                    ls,
                    rs,
                    l_serial,
                    r_serial,
                    e : self,
                    result : EqShort,
                }.step(tc)
            },
            (Local {..}, Local {..}) => (NeShort, Step::new_pfind(tc)),
            _ => unreachable!("Checked pattern match @ def_eq_local")
        }
    }        

    

    fn def_eq_app(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (EqResult, Step<DefEqAppZst>) {
        match (self.read(tc), other.read(tc)) {
            (App {..}, App {..}) => {
                let ((l_fun, l_args), h1) = self.unfold_apps(tc);
                let ((r_fun, r_args), h2) = other.unfold_apps(tc);
                match l_fun.try_def_eq(r_fun, tc) {
                    (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                    (EqShort, h3) => match try_args_eq(l_args, r_args, tc) {
                        (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                        (EqShort, h4) => {
                            DefEqApp::Base {
                                l : self,
                                r : other,
                                l_fun,
                                r_fun,
                                l_args,
                                r_args,
                                result : EqShort,
                                h1,
                                h2,
                                h3,
                                h4
                            }.step(tc)
                        }
                    }
                }
            },
            _ => unreachable!("Checked pattern match @ def_eq_app")
        }
    }        

    fn def_eq_eta(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (EqResult, Step<DefEqEtaZst>) {
        match (self.read(tc), other.read(tc)) {
            (_, Lambda {..}) => unreachable!("Checked pattern match @ def_eq_eta"),
            (Lambda { b_name : ln, b_type : lt, b_style : ls, body : lb, .. }, _) => {
                let (other_type_unred, h1) = other.infer(InferOnly, tc);
                let (other_type, h2) = other_type_unred.whnf(tc);
                match other_type.read(tc) {
                    Pi { b_name : rn, b_type : rt, b_style : rs, body : rb, .. } => {
                        let new_body = other.new_app(<ExprPtr>::new_var(0, tc), tc);
                        let new_lambda = <ExprPtr>::new_lambda(rn, rt, rs, new_body, tc);
                        let (result, h3) = self.try_def_eq(new_lambda, tc);
                        DefEqEta::Base {
                            r : other,
                            ln,
                            rn,
                            lt,
                            rt,
                            ls,
                            rs,
                            lb,
                            rb,
                            r_type_unred : other_type_unred,
                            r_type_red : other_type,
                            l_lambda : self,
                            r_lambda : new_lambda,
                            result,
                            h1,
                            h2,
                            h3,
                        }.step(tc)
                    },
                    _ => (NeShort, Step::new_pfind(tc)),
                }
            }
            _ => unreachable!("Checked pattern match @ def_eq_eta")
        }
    }    

}


// I don't think you need a `try` function for this since it's only
// ever called from other functios that are already wrapped in `try`
// such that control-flow can only short-circuit because of this.
#[has_try_eq(method = "args_eq(ls, rs, tc)")]
pub fn args_eq<'t, 'l : 't, 'e : 'l>(
    ls : ExprsPtr<'l>, 
    rs : ExprsPtr<'l>, 
    tc : &mut impl IsTc<'t, 'l, 'e>,
) -> (EqResult, Step<ArgsEqAuxZst>) {
    if let Some(cached) = tc.check_args_eq_cache(ls, rs) {
        cached
    } else {
        let ls_len = ls.len(tc);
        let rs_len = rs.len(tc);
        let result = match ls_len == rs_len {
            false => (NeShort, Step::new_pfind(tc)),
            true => match args_eq_aux(ls, rs, tc) {
                (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                (EqShort, h3) => (EqShort, h3),
            }
        };

        tc.insert_args_eq_cache(ls, rs, result);
        result
    }
}

fn args_eq_aux<'t, 'l : 't, 'e : 'l>(
    ls : ExprsPtr<'l>, 
    rs : ExprsPtr<'l>, 
    tc : &mut impl IsTc<'t, 'l, 'e>
) -> (EqResult, Step<ArgsEqAuxZst>) {
    match (ls.read(tc), rs.read(tc)) {
        (..) if ls == rs => {
            ArgsEqAux::Base {
                l : ls,
                r : rs,
                result : EqShort
            }.step(tc)
        },
        (Nil, Nil) => unreachable!("Should have been caught by refl"),
        (Cons(x, xs), Cons(y, ys)) => {
            match x.try_def_eq(y, tc) {
                (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                (EqShort, h1) => match args_eq_aux(xs, ys, tc) {
                    (NeShort, _) => (NeShort, Step::new_pfind(tc)),
                    (EqShort, h2) => {
                        ArgsEqAux::Step {
                            l_hd : x,
                            r_hd : y,
                            l_tl : xs,
                            r_tl : ys,
                            l : ls,
                            r : rs,
                            result : EqShort,
                            h1,
                            h2,
                        }.step(tc)
                    }
                }
            }
        },
        _ => unreachable!(
            "Unchecked and unequal list lengths in args_eq_aux; \
            should always be checked by `args_eq`"
        )
    }
}

