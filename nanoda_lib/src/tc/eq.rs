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


use EqResult::*;
use DeltaResult::*;




#[derive(Debug, Clone, Copy)]
pub enum EqResult<S> {
    EqShort(Step<S>),
    NeShort,
}

#[derive(Debug, Clone, Copy)]
pub enum DeltaResult<'a> {
    DeltaEq,
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}



#[macro_export]
macro_rules! filter_ne {
    ( $p:expr ) => {
        match $p {
            None => None,
            Some(NeShort) => return None,
            Some(EqResult::EqShort(step)) => Some(step)
        }
    };
}


impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
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
    // Doesn't need `try`; ensured by proof_irrel_eq
    fn is_sort_zero(
        self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<Step<IsSortZero<'l>>> {
        let (whnfd, h1) = self.whnf(tc);
        match whnfd.read(tc) {
            Sort { level } if level.is_zero_lit(tc).0 => {
                Some(IsSortZero::Base {
                    e : self,
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
    ) -> Option<(ExprPtr<'l>, Step<IsProposition<'l>>)> {
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
    ) -> Option<EqResult<ProofIrrelEq<'l>>> {
        let (l_type, h1) = self.is_proof(tc)?;
        let (r_type, h2) = other.is_proof(tc)?;
        match l_type.def_eq(r_type, tc) {
            None => Some(NeShort),
            Some(h3) => {
                Some(EqShort(ProofIrrelEq::Base {
                    l : self,
                    r : other,
                    l_type,
                    r_type,
                    h1,
                    h2,
                    h3
                }.step_only(tc)))
            }
        }
    }    
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

    ** The main `def_eq` and `def_eq_core` functions return None
    in the case that self and other are not equal, since a typechecker
    should never actually get/log disequal terms.

    The try-functions return `None` in the case that a certain pattern
    doesn't match.

    
    */
    #[has_try(method = "self.def_eq(other, tc)")]
    pub fn def_eq<TC : IsTc<'t, 'l, 'e>>(
        self,
        other : Self,
        tc : &mut TC,
    ) -> Option<Step<DefEq<'l>>> {
        if self == other {
            Some(DefEq::PtrEq {
                l : self,
                r : other,
            }.step_only(tc))
        } else if let Some(h1) = tc.check_eq_cache(self, other) {
            Some(DefEq::CacheHit {
                l : self,
                r : other,
                h1,
            }.step_only(tc))
        } else if let Some (result_step) = self.def_eq_core(other, tc) {
            tc.insert_eq_cache(self, other, result_step);
            Some(result_step)
        } else {
            None
        }
    }

    fn def_eq_core<TC : IsTc<'t, 'l, 'e>>(
        self,
        other : Self,
        tc : &mut TC,
    ) -> Option<Step<DefEq<'l>>> {
        let (l_w, h1) = self.whnf_core(tc);
        let (r_w, h2) = other.whnf_core(tc);

        let result_step = 
        if let Some(h3) = filter_ne!(l_w.try_def_eq_sort(r_w, tc)) {
            DefEq::Sort {
                l : self,
                r : other,
                l_w,
                r_w,
                h1,
                h2,
                h3
            }.step_only(tc)
        } else if let Some(h3) = filter_ne!(l_w.try_def_eq_pi(r_w, tc)) {
            DefEq::Pi {
                l : self,
                r : other,
                l_w,
                r_w,
                h1,
                h2,
                h3
            }.step_only(tc)
        } else if let Some(h3) = filter_ne!(l_w.try_def_eq_lambda(r_w, tc)) {
            DefEq::Lambda {
                l : self,
                r : other,
                l_w,
                r_w,
                h1,
                h2,
                h3
            }.step_only(tc)
        } else if let Some(h3) = filter_ne!(l_w.try_proof_irrel_eq(r_w, tc)) {
            DefEq::ProofIrrelEq {
                l : self,
                r : other,
                l_w,
                r_w,
                h1,
                h2,
                h3
            }.step_only(tc)
        } else {
            // for delta_result, `None` is disequality
            let (delta_result, h3) = l_w.lazy_delta_step(r_w, tc)?;
            match delta_result {
                DeltaEq => {
                    DefEq::DeltaShort {
                        l : self,
                        r : other,
                        l_w,
                        r_w,
                        h1,
                        h2,
                        h3
                    }.step_only(tc)
                },
                Exhausted(l_d, r_d) => {
                    if let Some(h4) = l_d.try_def_eq_const(r_d, tc) {
                        DefEq::EqConst {
                            l : self,
                            r : other,
                            l_w,
                            r_w,
                            l_d,
                            r_d,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step_only(tc)
                    } else if let Some(h4) = l_d.try_def_eq_local(r_d, tc) {
                        DefEq::EqLocal {
                            l : self,
                            r : other,
                            l_w,
                            r_w,
                            l_d,
                            r_d,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step_only(tc)

                    } else if let Some(h4) = l_d.try_def_eq_app(r_d, tc) {
                        DefEq::EqApp {
                            l : self,
                            r : other,
                            l_w,
                            r_w,
                            l_d,
                            r_d,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step_only(tc)
                    } else if let Some(h4) = l_d.try_def_eq_eta(r_d, tc) {
                        DefEq::EtaLr {
                            l : self,
                            r : other,
                            l_w,
                            r_w,
                            l_d,
                            r_d,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step_only(tc)
                    } else if let Some(h4) = r_d.try_def_eq_eta(l_d, tc) {
                        DefEq::EtaRl {
                            l : self,
                            r : other,
                            l_w,
                            r_w,
                            l_d,
                            r_d,
                            h1,
                            h2,
                            h3,
                            h4
                        }.step_only(tc)
                    } else {
                        return None
                    }
                }
            }
        };

        tc.insert_eq_cache(self, other, result_step);
        Some(result_step)
    }

    
    /*
    Although this exists as a separate function,
    it's also a constructor for steps of LazyDeltaStep.
    */
    pub fn lazy_delta_recurse(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(DeltaResult<'l>, Step<LazyDeltaStep<'l>>)> {
        if let Some(h1) = filter_ne!(self.try_def_eq_sort(other, tc)) {
            Some(LazyDeltaStep::Sort {
                l : self,
                r : other,
                result : DeltaEq,
                h1
            }.step(tc))
        } else if let Some(h1) = filter_ne!(self.try_def_eq_pi(other, tc)) {
            Some(LazyDeltaStep::Pi {
                l : self,
                r : other,
                result : DeltaEq,
                h1
            }.step(tc))
         } else if let Some(h1) = filter_ne!(self.try_def_eq_lambda(other, tc)) {
             Some(LazyDeltaStep::Lambda {
                 l : self,
                 r : other,
                 result : DeltaEq,
                 h1
             }.step(tc))
        } else {
            self.lazy_delta_step(other, tc)
        }
    }
            
    // return of `None` is NeqShort
    pub fn lazy_delta_step(
        self : Self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<(DeltaResult<'l>, Step<LazyDeltaStep<'l>>)> {
        let maybe_l_delta = self.try_is_delta(tc);
        let maybe_r_delta = other.try_is_delta(tc);

        match (maybe_l_delta, maybe_r_delta) {
            (None, None) => {
                Some(LazyDeltaStep::NoneNone {
                    l : self,
                    r : other,
                    result : Exhausted(self, other)
                }.step(tc))
            },
            (Some((l_def, h1)), None) => {
                let (l_defval_unred, h2) = self.unfold_def(tc).expect("lazy_delta1");
                let (l_defval, h3) = l_defval_unred.whnf_core(tc);
                let (result, h4) = l_defval.lazy_delta_recurse(other, tc)?;
                Some(LazyDeltaStep::SomeNone {
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
                }.step(tc))
            },
            (None, Some((r_def, h1))) => {
                let (r_defval_unred, h2) = other.unfold_def(tc).expect("lazy_delta2");
                let (r_defval, h3) = r_defval_unred.whnf_core(tc);
                let (result, h4) = self.lazy_delta_recurse(r_defval, tc)?;
                Some(LazyDeltaStep::NoneSome {
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
                }.step(tc))
            },
            (Some((l_def, h1)), Some((r_def, h2))) 
            if l_def.get_hint(tc) < r_def.get_hint(tc) => {
                let l_hint = l_def.get_hint(tc);
                let r_hint = r_def.get_hint(tc);
                let (r_defval_unred, h3) = other.unfold_def(tc).expect("lazy_delta3");
                let (r_defval, h4) = r_defval_unred.whnf_core(tc);
                let (result, h5) = self.lazy_delta_recurse(r_defval, tc)?;
                Some(LazyDeltaStep::Lt {
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
                }.step(tc))
            },
            (Some((l_def, h1)), Some((r_def, h2))) 
            if l_def.get_hint(tc) > r_def.get_hint(tc) => {
                let l_hint = l_def.get_hint(tc);
                let r_hint = r_def.get_hint(tc);
                let (l_defval_unred, h3) = self.unfold_def(tc).expect("lazy_delta4");
                let (l_defval, h4) = l_defval_unred.whnf_core(tc);
                let (result, h5) = l_defval.lazy_delta_recurse(other, tc)?;
                Some(LazyDeltaStep::Gt {
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
                }.step(tc))                
            },
            (Some((l_def, h1)), Some((r_def, h2))) => {
                assert_eq!(l_def.get_hint(tc), r_def.get_hint(tc));
                if let (App {..}, App {..}) = (self.read(tc), other.read(tc)) {
                    if l_def == r_def {
                        let ((l_fun, l_args), h3) = self.unfold_apps(tc);
                        let ((r_fun, r_args), h4) = other.unfold_apps(tc);
                        if let (
                            Some((lc_name, lc_levels)), 
                            Some((rc_name, rc_levels))
                         ) = (l_fun.try_const_info(tc), r_fun.try_const_info(tc)) {
                             match args_eq(l_args, r_args, tc) {
                                 NeShort => return None,
                                 EqShort(h5) => {
                                    let (levels_eq, h6) = lc_levels.eq_antisymm_many(rc_levels, tc);
                                    if levels_eq {
                                        return Some(LazyDeltaStep::Extensional {
                                            l : self,
                                            r : other,
                                            lc_name,
                                            rc_name,
                                            lc_levels,
                                            rc_levels,
                                            l_args,
                                            r_args,
                                            l_def,
                                            r_def,
                                            result : DeltaEq,
                                            h1,
                                            h2,
                                            h3,
                                            h4,
                                            h5,
                                            h6
                                        }.step(tc))
                                    }
                                 }
                             }
                        }
                    }
                }
        
                let (l_defval_unred, h1) = self.unfold_def(tc).expect("heights_eq 1");
                let (r_defval_unred, h2) = other.unfold_def(tc).expect("heights_eq 2");
                let (l_defval, h3) = l_defval_unred.whnf_core(tc);
                let (r_defval, h4) = r_defval_unred.whnf_core(tc);
                let (result, h5) = l_defval.lazy_delta_recurse(r_defval, tc)?;
                Some(LazyDeltaStep::Owise {
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
                }.step(tc))
            },
        }
    }    


    



    fn try_def_eq_sort(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> Option<EqResult<DefEqSort<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (Sort { level : l1 }, Sort { level : l2 }) => {
                let (ls_eq, h1) = l1.eq_antisymm(l2, tc);
                match ls_eq {
                    false => Some(NeShort),
                    true => Some(EqShort(
                        DefEqSort::Base {
                            l1,
                            l2,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : other,
                        }.step_only(tc))),
                }
            },
            _ => None
        }
    }

    // `try` is different here since this wrapper function
    // will do nothing if we don't have Pis, and if we do,
    // it will execute either with a Pfinder, or with a Tc
    // that knows this is supposed to return EqShort
    fn try_def_eq_pi(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> Option<EqResult<DefEqPi<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (Pi {..}, Pi {..}) => Some(self.def_eq_pi(other, Nil::<Expr>.alloc(tc), tc)),
            _ => None
        }
    }



    #[allow(unconditional_recursion)]
    fn def_eq_pi(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> EqResult<DefEqPi<'l>> {
        match (self.read(tc), other.read(tc)) {
            (
                Pi { b_name : ln, b_type : lt, b_style : ls, body : lb, .. },
                Pi { b_name : rn, b_type : rt, b_style : rs, body : rb, .. }
            ) => {
                let (lt_prime, h1) = lt.inst(doms, tc);
                let (rt_prime, h2) = rt.inst(doms, tc);
                match lt_prime.def_eq(rt_prime, tc) {
                    None => NeShort,
                    Some(h3) => {
                        let local = <ExprPtr>::new_local(ln, lt_prime, ls, tc);
                        let doms_prime = Cons(local, doms).alloc(tc);
                        match lb.def_eq_pi(rb, doms_prime, tc) {
                            NeShort => NeShort,
                            EqShort(h4) => {
                                EqShort(DefEqPi::Step {
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
                                    local,
                                    h1,
                                    h2,
                                    h3,
                                    h4,
                                    ind_arg1 : self,
                                    ind_arg2 : other
                                }.step_only(tc))
                            }
                        }
                    }
                }
            },
            // if no longer pis...
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                match l_prime.def_eq(r_prime, tc) {
                    None => NeShort,
                    Some(h3) => {
                        EqShort(DefEqPi::Base {
                            l : self,
                            r : other,
                            l_prime,
                            r_prime,
                            doms,
                            h1,
                            h2,
                            h3
                        }.step_only(tc))
                    },
                }
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
    ) -> Option<EqResult<DefEqLambda<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (Lambda {..}, Lambda {..}) => Some(self.def_eq_lambda(other, Nil::<Expr>.alloc(tc), tc)),
            _ => None
        }
    }

    
    #[allow(unconditional_recursion)]
    fn def_eq_lambda(
        self,
        other : Self,
        doms : ExprsPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e> 
    ) -> EqResult<DefEqLambda<'l>> {
        match (self.read(tc), other.read(tc)) {
            (
                Lambda { b_name : ln, b_type : lt, b_style : ls, body : lb, .. },
                Lambda { b_name : rn, b_type : rt, b_style : rs, body : rb, .. }
            ) => {
                let (lt_prime, h1) = lt.inst(doms, tc);
                let (rt_prime, h2) = rt.inst(doms, tc);
                match lt_prime.def_eq(rt_prime, tc) {
                    None => NeShort,
                    Some(h3) => {
                        let local = <ExprPtr>::new_local(ln, lt_prime, ls, tc);
                        let doms_prime = Cons(local, doms).alloc(tc);
                        match lb.def_eq_lambda(rb, doms_prime, tc) {
                            NeShort => NeShort,
                            EqShort(h4) => {
                                EqShort(DefEqLambda::Step {
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
                                    local,
                                    h1,
                                    h2,
                                    h3,
                                    h4,
                                    ind_arg1 : self,
                                    ind_arg2 : other
                                }.step_only(tc))
                            }
                        }
                    }
                }
            },
            // if no longer lambdas...
            _ => {
                let (l_prime, h1) = self.inst(doms, tc);
                let (r_prime, h2) = other.inst(doms, tc);
                match l_prime.def_eq(r_prime, tc) {
                    None => NeShort,
                    Some(h3) => {
                        EqShort(DefEqLambda::Base {
                            l : self,
                            r : other,
                            l_prime,
                            r_prime,
                            doms,
                            h1,
                            h2,
                            h3
                        }.step_only(tc))
                    },
                }
            }
        }
    }

    
    fn try_def_eq_const(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    //) -> Option<EqResult<DefEqConst<'l>>> {
    ) -> Option<Step<DefEqConst<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (
                Const { name : l_name, levels : l_levels }, 
                Const { name : r_name, levels : r_levels }
            ) if l_name == r_name => {
                match l_levels.eq_antisymm_many(r_levels, tc) {
                    (false, _) => None,
                    (true, h1) => {
                        Some(DefEqConst::Base {
                            l_name,
                            r_name,
                            l_levels,
                            r_levels,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : other
                        }.step_only(tc))
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
    //) -> Option<EqResult<DefEqLocal<'l>>> {
    ) -> Option<Step<DefEqLocal<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (
                Local { b_name : ln, b_type : lt, b_style : ls, serial : l_serial }, 
                Local { b_name : rn, b_type : rt, b_style : rs, serial : r_serial }
            ) if l_serial == r_serial => {
                Some(DefEqLocal::Base {
                    ln,
                    rn,
                    lt,
                    rt,
                    ls,
                    rs,
                    l_serial,
                    r_serial,
                    ind_arg1 : self,
                    ind_arg2 : other,
                }.step_only(tc))
            },
            _ => None
        }
    }        

    

    fn try_def_eq_app(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>
    //) -> Option<EqResult<DefEqApp<'l>>> {
    ) -> Option<Step<DefEqApp<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (App {..}, App {..}) => {
                let ((l_fun, l_args), h1) = self.unfold_apps(tc);
                let ((r_fun, r_args), h2) = other.unfold_apps(tc);
                let h3 = l_fun.def_eq(r_fun, tc)?;

                match args_eq(l_args, r_args, tc) {
                    NeShort => None,
                    EqShort(h4) => {
                        Some(DefEqApp::Base {
                            l_fun,
                            r_fun,
                            l_args,
                            r_args,
                            h1,
                            h2,
                            h3,
                            h4,
                            ind_arg1 : self,
                            ind_arg2 : other,
                        }.step_only(tc))
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
    //) -> Option<EqResult<DefEqEta<'l>>> {
    ) -> Option<Step<DefEqEta<'l>>> {
        match (self.read(tc), other.read(tc)) {
            (_, Lambda {..}) => None,
            (Lambda { b_name : ln, b_type : lt, b_style : ls, body : lb, .. }, _) => {
                let (other_type_unred, h1) = other.infer(InferOnly, tc);
                let (other_type, h2) = other_type_unred.whnf(tc);
                match other_type.read(tc) {
                    Pi { b_name : rn, b_type : rt, b_style : rs, body : rb, .. } => {
                        let new_body = other.new_app(<ExprPtr>::new_var(0, tc), tc);
                        let new_lambda = <ExprPtr>::new_lambda(rn, rt, rs, new_body, tc);
                        let h3 = self.def_eq(new_lambda, tc)?;
                        Some(DefEqEta::Base {
                            r : other,
                            ln,
                            rn,
                            lt,
                            rt,
                            ls,
                            rs,
                            lb,
                            rb,
                            h1,
                            h2,
                            h3,
                            ind_arg1 : self,
                        }.step_only(tc))
                    },
                    _ => None
                }
            }
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
) -> EqResult<ArgsEq<'l>> {
    let (ls_len, h1) = ls.len(tc);
    let (rs_len, h2) = rs.len(tc);
    match ls_len == rs_len {
        false => NeShort,
        true => match args_eq_aux(ls, rs, tc) {
            NeShort => NeShort,
            EqShort(h3) => {
                EqShort(ArgsEq::Base {
                    ls,
                    rs,
                    ls_len,
                    rs_len,
                    h1,
                    h2,
                    h3,
                }.step_only(tc))
            }
        }
    }
}

fn args_eq_aux<'t, 'l : 't, 'e : 'l>(
    ls : ExprsPtr<'l>, 
    rs : ExprsPtr<'l>, 
    tc : &mut impl IsTc<'t, 'l, 'e>
) -> EqResult<ArgsEqAux<'l>> {
    match (ls.read(tc), rs.read(tc)) {
        (Nil, Nil) => {
            EqShort(ArgsEqAux::Base {
                ind_arg1 : ls,
                ind_arg2 : rs
            }.step_only(tc))
        },
        (Cons(x, xs), Cons(y, ys)) => {
            match x.def_eq(y, tc) {
                None => NeShort,
                Some(h1) => match args_eq_aux(xs, ys, tc) {
                    NeShort => NeShort,
                    EqShort(h2) => {
                        EqShort(ArgsEqAux::Step {
                            x,
                            y,
                            xs,
                            ys,
                            h1,
                            h2,
                            ind_arg1 : ls,
                            ind_arg2 : rs,
                        }.step_only(tc))
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

