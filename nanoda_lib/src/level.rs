use nanoda_macros::has_try_bool;
use crate::levels;
use crate::name::NamePtr;
use crate::expr::{ Expr::*, ExprPtr };
use crate::trace::IsTracer;
use crate::trace::steps::*;
use crate::utils::{ 
    IsTc,
    Ptr, 
    List, 
    List::*, 
    ListPtr, 
    IsCtx, 
    IsLiveCtx,
    Store, 
    Env, 
    LiveZst, 
    HasNanodaDbg
};


pub type LevelPtr<'a> = Ptr<'a, Level<'a>>;
pub type LevelsPtr<'a> = ListPtr<'a, Level<'a>>;

use Level::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level<'a> {
    Zero,
    Succ(LevelPtr<'a>),
    Max(LevelPtr<'a>, LevelPtr<'a>),
    Imax(LevelPtr<'a>, LevelPtr<'a>),
    Param(NamePtr<'a>)
}

// You can never alloc somewhere higher/shorter lived than where you already are,
// but for insert_env you can alloc down/longer lived
// *** You can only be sure you've squashed to a lower one by DIRECTLY accessing
// a specific store, like Env or something, since in this case you can't be sure
// that the children are longer lived (even though they are.)
impl<'a> Level<'a> {
    pub fn insert_env<'e>(
        self, 
        env : &mut Env<'e, impl 'e + IsTracer>, 
        live : &Store<LiveZst>
    ) -> LevelPtr<'e> {
        let r = match self {
            Zero => unreachable!("Level::insert_Env(), Zero should always be in Env"),
            Succ(pred) => pred.insert_env(env, live).new_succ(env),
            Max(l, r) => {
                let l = l.insert_env(env, live);
                let r = r.insert_env(env, live);
                l.new_max(r, env)
            }
            Imax(l, r) => {
                let l = l.insert_env(env, live);
                let r = r.insert_env(env, live);
                l.new_imax(r, env)
            },
            Param(n) => n.insert_env(env, live).new_param(env)
        };
        assert!(r.in_env());
        r          
    }
}

impl<'a> LevelPtr<'a> {
    pub fn new_succ(self, ctx : &mut impl IsCtx<'a>) -> LevelPtr<'a> {
        Succ(self).alloc(ctx)
    }

    pub fn new_max(self, other : Self, ctx : &mut impl IsCtx<'a>) -> LevelPtr<'a> {
        Max(self, other).alloc(ctx)
    }
    
    pub fn new_imax(self, other : Self, ctx : &mut impl IsCtx<'a>) -> LevelPtr<'a> {
        Imax(self, other).alloc(ctx)
    }

    pub fn new_sort(self, ctx : &mut impl IsCtx<'a>) -> ExprPtr<'a> {
        Sort { level : self }.alloc(ctx)
    }


    pub fn is_param(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsParamZst>) {
        match self.read(ctx) {
            Zero => {
                IsParam::Zero {
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Succ(l) => {
                IsParam::Succ {
                    l,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Max(l, r) => {
                IsParam::Max {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Imax(l, r) => {
                IsParam::Imax {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Param(n) => {
                IsParam::Param {
                    n,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            }
        }
    }

    pub fn is_zero_lit(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsZeroLitZst>) {
        match self.read(ctx) {
            Zero => {
                IsZeroLit::Zero {
                    l : self,
                    result : true
                }.step(ctx)
            }
            Succ(pred) => {
                IsZeroLit::Succ {
                    pred,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Max(fst, snd) => {
                IsZeroLit::Max {
                    fst,
                    snd,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Imax(fst, snd) => {
                IsZeroLit::Imax {
                    fst,
                    snd,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Param(n) => {
                IsZeroLit::Param {
                    n,
                    l : self,
                    result : false,
                }.step(ctx)
            }
        }
    }

    pub fn is_succ(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsSuccZst>) {
        match self.read(ctx) {
            Zero => {
                IsSucc::Zero {
                    l : self,
                    result : false
                }.step(ctx)
            }
            Succ(pred) => {
                IsSucc::Succ {
                    pred : pred,
                    l : self,
                    result : true,
                }.step(ctx)
            },
            Max(fst, snd) => {
                IsSucc::Max {
                    fst,
                    snd,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Imax(fst, snd) => {
                IsSucc::Imax {
                    fst,
                    snd,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Param(n) => {
                IsSucc::Param {
                    n,
                    l : self,
                    result : false,
                }.step(ctx)
            }        
        }
    }    

    pub fn is_any_max(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsAnyMaxZst>) {
        match self.read(ctx) {
            Zero => {
                IsAnyMax::Zero {
                    l : self,
                    result : false
                }.step(ctx)
            }
            Succ(pred) => {
                IsAnyMax::Succ {
                    pred,
                    l : self,
                    result : false,
                }.step(ctx)
            },
            Max(fst, snd) => {
                IsAnyMax::Max {
                    fst,
                    snd,
                    l : self,
                    result : true,
                }.step(ctx)
            },
            Imax(fst, snd) => {
                IsAnyMax::Imax {
                    fst,
                    snd,
                    l : self,
                    result : true,
                }.step(ctx)
            },
            Param(n) => {
                IsAnyMax::Param {
                    n,
                    l : self,
                    result : false,
                }.step(ctx)
            }        
        }
    }        

    pub fn combining(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> (Self, Step<CombiningZst>) {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, _) => {
                Combining::Lzero {
                    r : other,
                    l : self,
                    result : other,
                }.step(ctx)
            }
            (_, Zero) => {
                Combining::Rzero {
                    l : self,
                    r : other,
                    result : self,
                }.step(ctx)
            }
            (Succ(l_pred), Succ(r_pred)) => {
                let (result_prime, h1) = l_pred.combining(r_pred, ctx);
                let result = result_prime.new_succ(ctx);
                Combining::Succ {
                    l_pred,
                    r_pred,
                    result_prime,
                    l : self,
                    r : other,
                    result,
                    h1
                }.step(ctx)
            }
            _ => {
                let (_, h1) = self.is_zero_lit(ctx);
                let (_, h2) = other.is_zero_lit(ctx);
                let (_, h3) = self.is_succ(ctx);
                let (_, h4) = other.is_succ(ctx);
                Combining::Owise {
                    l : self,
                    r : other,
                    result : self.new_max(other, ctx),
                    h1,
                    h2,
                    h3,
                    h4,
                }.step(ctx)
            }
        }
    }    

    
    pub fn simplify(self, ctx : &mut impl IsLiveCtx<'a>) -> (Self, Step<SimplifyZst>) {
        match self.read(ctx) {
            Zero => {
                Simplify::Zero {
                    l : self,
                    result : self,
                }.step(ctx)
            }
            Param(n) => {
                Simplify::Param {
                    n,
                    l : self,
                    result : self,
                }.step(ctx)
            }
            Succ(pred) => {
                let (pred_prime, h1) = pred.simplify(ctx);
                let result = pred_prime.new_succ(ctx);

                Simplify::Succ {
                    pred,
                    pred_prime,
                    l : self,
                    result,
                    h1,
                }.step(ctx)
            }
            Max(fst, snd) => {
                let (fst_prime, h1) = fst.simplify(ctx);
                let (snd_prime, h2) = snd.simplify(ctx);
                let (result, h3) = fst_prime.combining(snd_prime, ctx);
                Simplify::Max {
                    fst,
                    snd,
                    fst_prime,
                    snd_prime,
                    result,
                    l : self,
                    h1,
                    h2,
                    h3,
                }.step(ctx)
            },
            Imax(fst, snd) => {
                let (snd_prime, h1) = snd.simplify(ctx);
                match snd_prime.read(ctx) {
                    Zero => {
                        Simplify::ImaxZero {
                            fst,
                            snd,
                            snd_prime,
                            l : self,
                            result : snd_prime,
                            h1,
                        }.step(ctx)
                    }
                    Succ(r_prime) => {
                        let (fst_prime, h2) = fst.simplify(ctx);
                        let (x, h3) = fst_prime.combining(snd_prime, ctx);
                        Simplify::ImaxSucc {
                            fst,
                            snd,
                            fst_prime,
                            snd_prime : r_prime,
                            result : x,
                            l : self,
                            succ_snd_prime : snd_prime,
                            h1,
                            h2,
                            h3,
                        }.step(ctx)
                    }
                    _ => {
                        let r_prime = snd_prime;
                        let (_, h2) = r_prime.is_zero_lit(ctx);
                        let (_, h3) = r_prime.is_succ(ctx);
                        let (l_prime, h4) = fst.simplify(ctx);
                        let result = l_prime.new_imax(r_prime, ctx);
                        Simplify::ImaxOwise {
                            fst,
                            snd,
                            fst_prime : l_prime,
                            snd_prime : r_prime,
                            l : self,
                            result,
                            h1,
                            h2,
                            h3,
                            h4,
                        }.step(ctx)
                    }
                }
            }
        }
    }    

    // for some level `l` and list of params `ps`,
    // assert that :
    // `forall Level::Param(n) \in l, Level::Param(n) \in ps`
    pub fn params_defined(
        self, 
        params : LevelsPtr<'a>, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<ParamsDefinedZst>) {
        match self.read(ctx) {
            Zero => {
                ParamsDefined::Zero {
                    params,
                    l : self,
                    result : true
                }.step(ctx)
            },
            Succ(pred) => {
                let (out, h1) = pred.params_defined(params, ctx);
                ParamsDefined::Succ {
                    pred,
                    params,
                    l : self,
                    result : out,
                    h1,
                }.step(ctx)
            },
            Max(l, r) => {
                let (out_l, h1) = l.params_defined(params, ctx);
                let (out_r, h2) = r.params_defined(params, ctx);
                let out = out_l && out_r;
                ParamsDefined::Max {
                    fst : l,
                    snd : r,
                    params,
                    l : self,
                    result : out,
                    h1,
                    h2,
                }.step(ctx)
            }
            Imax(l, r) => {
                let (out_l, h1) = l.params_defined(params, ctx);
                let (out_r, h2) = r.params_defined(params, ctx);
                let out = out_l && out_r;
                ParamsDefined::Imax {
                    fst : l,
                    snd : r,
                    params,
                    l : self,
                    result : out,
                    h1,
                    h2,
                }.step(ctx)
            }
            Param(n) => match params.read(ctx) {
                Nil => unreachable!("All params must be defined!"),
                Cons(hd, tl) if self == hd => {
                    ParamsDefined::BaseParam {
                        n,
                        tl,
                        l : self,
                        params,
                        result : true
                    }.step(ctx)
                },
                Cons(hd, tl) => {
                    let (out, h1) = self.params_defined(tl, ctx);
                    ParamsDefined::StepParam {
                        n,
                        hd,
                        tl,
                        l : self,
                        params,
                        result : out,
                        h1,
                    }.step(ctx)
                }
            }
        }
    }

    pub fn subst(
        self,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (Self, Step<SubstLZst>) {
        match self.read(ctx) {
            Zero => {
                SubstL::Zero {
                    ks,
                    vs,
                    l : self,
                    l_prime : self,
                }.step(ctx)
            },
            Succ(pred) => {
                let (pred_prime, h1) = pred.subst(ks, vs, ctx);
                let l_prime = pred_prime.new_succ(ctx);
                SubstL::Succ {
                    pred,
                    pred_prime,
                    ks,
                    vs,
                    l : self,
                    l_prime,
                    h1,
                }.step(ctx)
            },
            Max(fst, snd) => {
                let (fst_prime, h1) = fst.subst(ks, vs, ctx);
                let (snd_prime, h2) = snd.subst(ks, vs, ctx);
                let lvl_prime = fst_prime.new_max(snd_prime, ctx);
                SubstL::Max {
                    fst,
                    snd,
                    fst_prime,
                    snd_prime,
                    l : self,
                    l_prime : lvl_prime,
                    ks,
                    vs,
                    h1,
                    h2,
                }.step(ctx)
            },
            Imax(fst, snd) => {
                let (fst_prime, h1) = fst.subst(ks, vs, ctx);
                let (snd_prime, h2) = snd.subst(ks, vs, ctx);
                let lvl_prime = fst_prime.new_imax(snd_prime, ctx);
                SubstL::Imax {
                    fst,
                    snd,
                    fst_prime,
                    snd_prime,
                    l : self,
                    l_prime : lvl_prime,
                    ks,
                    vs,
                    h1,
                    h2,
                }.step(ctx)                
            },
            Param(n) => match (ks.read(ctx), vs.read(ctx)) {
                (Nil, Nil) => {
                    SubstL::ParamNil {
                        n,
                        l : self,
                        nil : ks,
                    }.step(ctx)
                }
                (Cons(k, ks_tl), Cons(v, vs_tl)) if self == k => {
                    SubstL::ParamHit {
                        n,
                        v,
                        ks_tl,
                        vs_tl,
                        l : self,
                        ks,
                        vs,
                    }.step(ctx)
                }
                (Cons(k, ks_tl), Cons(v, vs_tl)) => {
                    let (l_prime, h1) = self.subst(ks_tl, vs_tl, ctx);
                    SubstL::ParamMiss {
                        n,
                        k,
                        v,
                        l_prime,
                        ks_tl,
                        vs_tl,
                        l : self,
                        ks,
                        vs,
                        h1,
                    }.step(ctx)
                }
                _ => unreachable!("level::subst must get lists of equal length!")
            }
        }
    }


    fn ensure_imax_leq(
        self, 
        lhs : Self,
        rhs : Self,
        l_h : usize,
        r_h : usize,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<EnsureImaxLeqZst>) {

        assert!(self.is_param(ctx).0);
        let i_snd_list = levels!([self], ctx);
        let zero_list = levels!([Zero.alloc(ctx)], ctx);
        let succ_list = levels!([self.new_succ(ctx)], ctx);

        let (l_z, h1) = lhs.subst(i_snd_list, zero_list, ctx);
        let (r_z, h2) = rhs.subst(i_snd_list, zero_list, ctx);
        let (l_z_prime, h3) = l_z.simplify(ctx);
        let (r_z_prime, h4) = r_z.simplify(ctx);
        let (b1, h5) = l_z_prime.leq_core(r_z_prime, l_h, r_h, ctx);

        let (l_s, h6) = lhs.subst(i_snd_list, succ_list, ctx);
        let (r_s, h7) = rhs.subst(i_snd_list, succ_list, ctx);
        let (l_s_prime, h8) = l_s.simplify(ctx);
        let (r_s_prime, h9) = r_s.simplify(ctx);
        let (b2, h10) = l_s_prime.leq_core(r_s_prime, l_h, r_h, ctx);
        let result = b1 && b2;

        EnsureImaxLeq::Base {
            i_snd : self,
            l : lhs,
            r : rhs,
            l_h,
            r_h,
            l_z,
            r_z,
            l_z_prime,
            r_z_prime,
            l_s,
            r_s,
            l_s_prime,
            r_s_prime,
            b1,
            b2,
            pp : i_snd_list,
            zz : zero_list,
            s_pp : succ_list,
            result,
            h1,
            h2,
            h3,
            h4,
            h5,
            h6,
            h7,
            h8,
            h9,
            h10
        }.step(ctx)

    }   

    fn leq_core(
        self,
        other : Self,
        l_h : usize,
        r_h : usize,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (bool, Step<LeqCoreZst>)  {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, _) if l_h <= r_h => {
                LeqCore::ZAny {
                    r : other,
                    l_h,
                    r_h,
                    l : self,
                    result : true
                }.step(ctx)
            },
            (_, Zero) if r_h < l_h => {
                LeqCore::AnyZ {
                    l : self,
                    l_h,
                    r_h,
                    r : other,
                    result : false
                }.step(ctx)
            },
            (Param(n1), Param(n2)) => {
                LeqCore::ParamParam {
                    n1,
                    n2,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result : ((n1 == n2) && (l_h <= r_h)),
                }.step(ctx)
            },
            (Param(n), Zero) => {
                LeqCore::ParamZero {
                    n,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result : false
                }.step(ctx)
            },
            (Zero, Param(n)) => {
                LeqCore::ZeroParam {
                    n,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result : l_h <= r_h
                }.step(ctx)
            },
            (Succ(pred), _) => {
                let (result, h1) = pred.leq_core(other, 1 + l_h, r_h, ctx);
                LeqCore::SuccAny {
                    l_pred : pred,
                    r : other,
                    l_h,
                    r_h,
                    result,
                    l_h_prime : 1 + l_h,
                    l : self,
                    h1,
                }.step(ctx)
            },
            (_, Succ(pred)) => {
                let (result, h1) = self.leq_core(pred, l_h, 1 + r_h, ctx);
                LeqCore::AnySucc {
                    l : self,
                    r_pred : pred,
                    l_h,
                    r_h,
                    result,
                    r_h_prime : 1 + r_h,
                    r : other,
                    h1,
                }.step(ctx)
            },
            (Max(fst, snd), _) => {
                let (b1, h1) = fst.leq_core(other, l_h, r_h, ctx);
                let (b2, h2) = snd.leq_core(other, l_h, r_h, ctx);
                let result = b1 && b2;
                LeqCore::MaxAny {
                    fst,
                    snd,
                    r : other,
                    l_h,
                    r_h,
                    b1,
                    b2,
                    l : self,
                    result,
                    h1,
                    h2,
                }.step(ctx)
            },
            (Param(n), Max(fst, snd)) => {
                let (b1, h1) = self.leq_core(fst, l_h, r_h, ctx);
                let (b2, h2) = self.leq_core(snd, l_h, r_h, ctx);
                let result = b1 || b2;
                LeqCore::ParamMax {
                    n,
                    fst,
                    snd,
                    b1,
                    b2,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result,
                    h1,
                    h2,
                }.step(ctx)
            },
            (Zero, Max(fst, snd)) => {
                let (b1, h1) = self.leq_core(fst, l_h, r_h, ctx);
                let (b2, h2) = self.leq_core(snd, l_h, r_h, ctx);
                let result = b1 || b2;
                LeqCore::ZeroMax {
                    fst,
                    snd,
                    b1,
                    b2,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result,
                    h1,
                    h2,
                }.step(ctx)
            },
            (Imax(a, b), Imax(x, y)) if a == b && x == y => {
                LeqCore::ImaxCongr {
                    fst : a,
                    snd : b,
                    l_h,
                    r_h,
                    l : self,
                    r : other,
                    result : true
                }.step(ctx)
            },
            (Imax(fst, snd), _) if snd.is_param(ctx).0 => {
                let n = match snd.read(ctx) {
                    Param(n) => n,
                    _ => unreachable!()
                };

                let (result, h1) = snd.ensure_imax_leq(self, other, l_h, r_h, ctx);
                LeqCore::ImaxParamL {
                    n,
                    fst,
                    r : other,
                    l_h,
                    r_h,
                    result,
                    snd,
                    l : self,
                    h1
                }.step(ctx)
            },
            (_, Imax(fst, snd)) if snd.is_param(ctx).0 => {
                let n = match snd.read(ctx) {
                    Param(n) => n,
                    _ => unreachable!()
                };

                let (result, h1) = snd.ensure_imax_leq(self, other, l_h, r_h, ctx);
                LeqCore::ImaxParamR {
                    n,
                    fst,
                    l : self,
                    l_h,
                    r_h,
                    result,
                    snd,
                    r : other,
                    h1
                }.step(ctx)
            },
            (Imax(a, b), _) if b.is_any_max(ctx).0 => match b.read(ctx) {
                Imax(c, d) => {
                    let im_a_d  = <Self>::new_imax(a, d, ctx); 
                    let im_c_d = <Self>::new_imax(c, d, ctx);
                    let new_max = <Self>::new_max(im_a_d, im_c_d, ctx);
                    let (result, h1) = new_max.leq_core(other, l_h, r_h, ctx);
                    LeqCore::ImaxImaxAny {
                        a,
                        c,
                        d,
                        r : other,
                        l_prime : new_max,
                        l : self,
                        l_h,
                        r_h,
                        result,
                        h1,
                    }.step(ctx)
                },
                Max(c, d) => {
                    let im_a_c = <Self>::new_imax(a, c, ctx);
                    let im_a_d = <Self>::new_imax(a, d, ctx);
                    let (new_max_prime, h1) = <Self>::new_max(im_a_c, im_a_d, ctx).simplify(ctx);
                    let (result, h2) = new_max_prime.leq_core(other, l_h, r_h, ctx);
                    LeqCore::ImaxMaxAny {
                        a,
                        c,
                        d,
                        r : other,
                        new_max_prime,
                        l_h,
                        r_h,
                        result,
                        l_prime : new_max_prime,
                        l : self,
                        h1,
                        h2,
                    }.step(ctx)
                },
                _ => unreachable!("checked pattern : ImaxParamL")
            },
                
            (_, Imax(x, y)) if y.is_any_max(ctx).0 => match y.read(ctx) {
                Imax(j, k) => {
                    let im_x_k = <Self>::new_imax(x, k, ctx);
                    let im_j_k = <Self>::new_imax(j, k, ctx);
                    let new_max = <Self>::new_max(im_x_k, im_j_k, ctx);                    
                    let (result, h1) = self.leq_core(new_max, l_h, r_h, ctx);
                    LeqCore::AnyImaxImax {
                        l : self,
                        x,
                        j,
                        k,
                        l_h,
                        r_h,
                        result,
                        r_prime : new_max,
                        r : other,
                        h1,
                    }.step(ctx)
                },
                Max(j, k) => {
                    let im_x_j = <Self>::new_imax(x, j, ctx);
                    let im_x_k = <Self>::new_imax(x, k, ctx);
                    let (new_max_prime, h1) = <Self>::new_max(im_x_j, im_x_k, ctx).simplify(ctx);                    
                    let (result, h2) = self.leq_core(new_max_prime, l_h, r_h, ctx);
                    LeqCore::AnyImaxMax {
                        l : self,
                        x,
                        j,
                        k,
                        new_max_prime,
                        l_h,
                        r_h,
                        result,
                        r_prime : new_max_prime,
                        r : other,
                        h1,
                        h2,
                    }.step(ctx)
                },
                _ => unreachable!("checked pattern : ImaxParamR")
            }
            _ => unreachable!("leq_core2")
        }
    }


    pub fn leq(
        self,
        other : LevelPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<LeqZst>) {
        let (l_prime, h1) = self.simplify(ctx);
        let (r_prime, h2) = other.simplify(ctx);
        let (res, h3) = l_prime.leq_core(r_prime, 0, 0, ctx);
        Leq::Base {
            l : self,
            r : other,
            l_prime,
            r_prime,
            b : res,
            h1,
            h2,
            h3,
        }.step(ctx)
    }




    pub fn is_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsZeroZst>) {
        let (b, h1) = self.leq(Zero.alloc(ctx), ctx);
        IsZero::Base {
            l : self,
            b,
            h1
        }.step(ctx)
    }

    pub fn is_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsNonzeroZst>) {
        let (b, h1) = Zero.alloc(ctx).new_succ(ctx).leq(self, ctx);
        IsNonzero::Base {
            l : self,
            b,
            h1,
        }.step(ctx)
    }

    pub fn maybe_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<MaybeZeroZst>) {
        let (is_nonzero, h1) = self.is_nonzero(ctx);
        MaybeZero::Base {
            l : self,
            b : !is_nonzero,
            h1
        }.step(ctx)
    }

    pub fn maybe_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<MaybeNonzeroZst>) {
        let (is_zero, h1) = self.is_zero(ctx);
        MaybeNonzero::Base {
            l : self,
            b : !is_zero,
            h1
        }.step(ctx)
    }
}

impl<'t, 'l : 't, 'e : 'l> LevelPtr<'l> {
    #[has_try_bool(method = "self.eq_antisymm(other, tc)")]
     pub fn eq_antisymm(
        self,
        other : LevelPtr<'l>,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (bool, Step<EqAntisymmZst>) {
        let (b1, h1) = self.leq(other, tc);
        let (b2, h2) = other.leq(self, tc);
        EqAntisymm::Base {
            l : self,
            r : other,
            b1,
            b2,
            result : b1 && b2,
            h1,
            h2,
        }.step(tc)
    }   

      pub fn assert_eq_antisymm(
        self,
        other : LevelPtr<'l>,
        tc : &mut impl IsLiveCtx<'l>,
    ) -> (bool, Step<EqAntisymmZst>) {
        let (b1, h1) = self.leq(other, tc);
        let (b2, h2) = other.leq(self, tc);
        EqAntisymm::Base {
            l : self,
            r : other,
            b1,
            b2,
            result : b1 && b2,
            h1,
            h2,
        }.step(tc)
    }      

    

}

impl<'t, 'l : 't, 'e : 'l> LevelsPtr<'l> {
    #[has_try_bool(method = "self.eq_antisymm_many(other, tc)")]
    pub fn eq_antisymm_many(
        self,
        other : Self,
        tc : &mut impl IsTc<'t, 'l, 'e>,
    ) -> (bool, Step<EqAntisymmManyZst>) {
        match (self.read(tc), other.read(tc)) {
            (Nil, Nil) => {
                EqAntisymmMany::Base {
                    ls : self,
                    rs : other,
                    result : true,
                }.step(tc)
            },
            (Cons(hd, tl), Nil) => {
                EqAntisymmMany::BaseFL {
                    hd,
                    tl,
                    ls : self,
                    rs : other,
                    result : false,
                }.step(tc)
            }
            (Nil, Cons(hd, tl)) => {
                EqAntisymmMany::BaseFR {
                    hd,
                    tl,
                    ls : self,
                    rs : other,
                    result : false
                }.step(tc)
            },
            (Cons(l_hd, l_tl), Cons(r_hd, r_tl)) => {
                let (b1, h1) = l_hd.try_eq_antisymm(r_hd, tc);
                let (b2, h2) = l_tl.try_eq_antisymm_many(r_tl, tc);
                EqAntisymmMany::Step {
                    l_hd,
                    r_hd,
                    l_tl,
                    r_tl,
                    b1,
                    b2,
                    ls : self,
                    rs : other,
                    result : b1 && b2,
                    h1,
                    h2,
                }.step(tc)
            },
        }
    }   

}

impl<'a> LevelsPtr<'a> {
    pub fn params_defined_many(
        self,
        dec_ups : LevelsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (bool, Step<ParamsDefinedManyZst>) {
        match self.read(ctx) {
            Nil => {
                ParamsDefinedMany::Base {
                    params : dec_ups,
                    ls  : self,
                    result : true
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (b1, h1) = tl.params_defined_many(dec_ups, ctx);
                let (b2, h2) = hd.params_defined(dec_ups, ctx);
                let out = b1 && b2;
                ParamsDefinedMany::Step {
                    hd,
                    tl,
                    params : dec_ups,
                    ls : self,
                    result : out,
                    h1,
                    h2,
                }.step(ctx)
            }
        }
    }

    pub fn subst_many(
        self,
        ks : Self,
        vs : Self,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (LevelsPtr<'a>, Step<SubstLManyZst>) {
        match self.read(ctx) {
            Nil => {
                SubstLMany::Base {
                    ls : self,
                    ks,
                    vs,
                    ls_prime : self,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (hd_prime, h1) = hd.subst(ks, vs, ctx);
                let (tl_prime, h2) = tl.subst_many(ks, vs, ctx);
                let ls_prime = Cons(hd_prime, tl_prime).alloc(ctx);
                SubstLMany::Step {
                    ls_hd : hd,
                    ls_hd_prime : hd_prime,
                    ls_tl : tl,
                    ls_tl_prime : tl_prime,
                    ks,
                    vs,
                    ls : self,
                    ls_prime,
                    h1,
                    h2,
                }.step(ctx)
            }
        }
    }


    pub fn fold_imaxs(
        self, 
        sink : LevelPtr<'a>, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (LevelPtr<'a>, Step<FoldImaxsZst>) {
        match self.read(ctx) {
            Nil => {
                FoldImaxs::Base {
                    l : sink,
                    ls : self,
                    result : sink,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let combined = <LevelPtr>::new_imax(hd, sink, ctx);
                let (result, h1) = tl.fold_imaxs(combined, ctx);
                FoldImaxs::Step {
                    hd,
                    tl,
                    l : sink,
                    result,
                    ls : self,
                    combined,
                    h1,
                }.step(ctx)
            }
        }
    }    
}

impl<'a> HasNanodaDbg<'a> for Level<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        match self {
            Zero => format!("0"),
            Succ(pred) => format!("S({})", pred.nanoda_dbg(ctx)),
            Max(l, r) => format!("M({}, {})", l.nanoda_dbg(ctx), r.nanoda_dbg(ctx)),
            Imax(l, r) => format!("Im({}, {})", l.nanoda_dbg(ctx), r.nanoda_dbg(ctx)),
            Param(n) => format!("{}", n.nanoda_dbg(ctx))
        }
    }
}


