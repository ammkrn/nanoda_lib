use crate::levels;
use crate::name::NamePtr;
use crate::expr::{ Expr::*, ExprPtr };
use crate::trace::IsTracer;
use crate::trace::steps::*;
use crate::utils::{ 
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
// *** You can only be sure you've squashed to a lower one by DIRECTLy accessing
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


    pub fn is_param(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsParam<'a>>) {
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


    pub fn is_zero_lit(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsZeroLit<'a>>) {
        match self.read(ctx) {
            Zero => {
                IsZeroLit::Zero {
                    ind_arg1 : self,
                    ind_arg2 : true
                }.step(ctx)
            }
            Succ(pred) => {
                IsZeroLit::Succ {
                    l : pred,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Max(l, r) => {
                IsZeroLit::Max {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Imax(l, r) => {
                IsZeroLit::Imax {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Param(n) => {
                IsZeroLit::Param {
                    n,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }
        }
    }

    pub fn is_succ(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsSucc<'a>>) {
        match self.read(ctx) {
            Zero => {
                IsSucc::Zero {
                    ind_arg1 : self,
                    ind_arg2 : false
                }.step(ctx)
            }
            Succ(pred) => {
                IsSucc::Succ {
                    l : pred,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            },
            Max(l, r) => {
                IsSucc::Max {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Imax(l, r) => {
                IsSucc::Imax {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Param(n) => {
                IsSucc::Param {
                    n,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }        
        }
    }    

    pub fn is_any_max(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsAnyMax<'a>>) {
        match self.read(ctx) {
            Zero => {
                IsAnyMax::Zero {
                    ind_arg1 : self,
                    ind_arg2 : false
                }.step(ctx)
            }
            Succ(pred) => {
                IsAnyMax::Succ {
                    l : pred,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            },
            Max(l, r) => {
                IsAnyMax::Max {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            },
            Imax(l, r) => {
                IsAnyMax::Imax {
                    l,
                    r,
                    ind_arg1 : self,
                    ind_arg2 : true,
                }.step(ctx)
            },
            Param(n) => {
                IsAnyMax::Param {
                    n,
                    ind_arg1 : self,
                    ind_arg2 : false,
                }.step(ctx)
            }        
        }
    }        

    pub fn combining(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> (Self, Step<Combining<'a>>) {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, r) => {
                let result = r.alloc(ctx);
                Combining::Lzero {
                    r : other,
                    ind_arg1 : self,
                }.step(ctx)
            }
            (l, Zero) => {
                let result = l.alloc(ctx);
                Combining::Rzero {
                    l : self,
                    ind_arg2 : other,
                }.step(ctx)
            }
            (Succ(l), Succ(r)) => {
                let (x, h1) = l.combining(r, ctx);
                let ind_arg3 = x.new_succ(ctx);
                Combining::Succ {
                    l,
                    r,
                    x,
                    h1,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    ind_arg3
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
                    h1,
                    h2,
                    h3,
                    h4,
                    ind_arg3 : self.new_max(other, ctx)
                }.step(ctx)
            }
        }
    }    

    
    pub fn simplify(self, ctx : &mut impl IsLiveCtx<'a>) -> (Self, Step<Simplify<'a>>) {
        match self.read(ctx) {
            Zero => {
                Simplify::Zero {
                    ind_arg1 : self,
                }.step(ctx)
            }
            Param(n) => {
                Simplify::Param {
                    n,
                    ind_arg1 : self,
                }.step(ctx)
            }
            Succ(l) => {
                let (l_prime, h1) = l.simplify(ctx);
                let ind_arg2 = l_prime.new_succ(ctx);

                Simplify::Succ {
                    l,
                    l_prime,
                    h1,
                    ind_arg1 : self,
                    ind_arg2,
                }.step(ctx)
            }
            Max(l, r) => {
                let (l_prime, h1) = l.simplify(ctx);
                let (r_prime, h2) = r.simplify(ctx);
                let (x, h3) = l_prime.combining(r_prime, ctx);
                Simplify::Max {
                    l,
                    r,
                    l_prime,
                    r_prime,
                    x,
                    h1,
                    h2,
                    h3,
                    ind_arg1 : self,
                }.step(ctx)
            },
            Imax(l, r) => {
                let (rsimp, h1) = r.simplify(ctx);
                match rsimp.read(ctx) {
                    Zero => {
                        Simplify::ImaxZero {
                            l,
                            r,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : rsimp,
                        }.step(ctx)
                    }
                    Succ(r_prime) => {
                        let (l_prime, h2) = l.simplify(ctx);
                        let (x, h3) = l_prime.combining(rsimp, ctx);
                        Simplify::ImaxSucc {
                            l,
                            r,
                            l_prime,
                            r_prime,
                            x,
                            h1,
                            h2,
                            h3,
                            ind_arg1 : self,
                        }.step(ctx)
                    }
                    _ => {
                        let r_prime = rsimp;
                        let (_, h2) = r_prime.is_zero_lit(ctx);
                        let (_, h3) = r_prime.is_succ(ctx);
                        let (l_prime, h4) = l.simplify(ctx);
                        let ind_arg2 = l_prime.new_imax(r_prime, ctx);
                        Simplify::ImaxOwise {
                            l,
                            r,
                            l_prime,
                            r_prime,
                            h1,
                            h2,
                            h3,
                            h4,
                            ind_arg1 : self,
                            ind_arg2,
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
    ) -> (bool, Step<ParamsDefined<'a>>) {
        match self.read(ctx) {
            Zero => {
                ParamsDefined::Zero {
                    params,
                    ind_arg1 : self,
                    out : true
                }.step(ctx)
            },
            Succ(pred) => {
                let (out, h1) = pred.params_defined(params, ctx);
                ParamsDefined::Succ {
                    pred,
                    params,
                    h1,
                    ind_arg1 : self,
                    out
                }.step(ctx)
            },
            Max(l, r) => {
                let (out_l, h1) = l.params_defined(params, ctx);
                let (out_r, h2) = r.params_defined(params, ctx);
                let out = out_l && out_r;
                ParamsDefined::Max {
                    l,
                    r,
                    params,
                    h1,
                    h2,
                    ind_arg1 : self,
                    out
                }.step(ctx)
            }
            Imax(l, r) => {
                let (out_l, h1) = l.params_defined(params, ctx);
                let (out_r, h2) = r.params_defined(params, ctx);
                let out = out_l && out_r;
                ParamsDefined::Imax {
                    l,
                    r,
                    params,
                    h1,
                    h2,
                    ind_arg1 : self,
                    out
                }.step(ctx)
            }
            Param(n) => match params.read(ctx) {
                Nil => unreachable!("All params must be defined!"),
                Cons(hd, tl) if self == hd => {
                    ParamsDefined::BaseParam {
                        n,
                        hd,
                        tl,
                        ind_arg1 : self,
                        ind_arg2 : params,
                        out : true
                    }.step(ctx)
                },
                Cons(hd, tl) => {
                    let (out, h1) = self.params_defined(tl, ctx);
                    ParamsDefined::StepParam {
                        n,
                        hd,
                        tl,
                        h1,
                        ind_arg1 : self,
                        ind_arg2 : params,
                        out
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
    ) -> (Self, Step<SubstL<'a>>) {
        match self.read(ctx) {
            Zero => {
                SubstL::Zero {
                    ks,
                    vs,
                    ind_arg1 : self,
                }.step(ctx)
            },
            Succ(pred) => {
                let (pred_prime, h1) = pred.subst(ks, vs, ctx);
                let ind_arg2 = pred_prime.new_succ(ctx);
                SubstL::Succ {
                    pred,
                    pred_prime,
                    ks,
                    vs,
                    h1,
                    ind_arg1 : self,
                    ind_arg2,
                }.step(ctx)
            },
            Max(l, r) => {
                let (l_prime, h1) = l.subst(ks, vs, ctx);
                let (r_prime, h2) = r.subst(ks, vs, ctx);
                let ind_arg2 = l_prime.new_max(r_prime, ctx);
                SubstL::Max {
                    l,
                    r,
                    l_prime,
                    r_prime,
                    ks,
                    vs,
                    h1,
                    h2,
                    ind_arg1 : self,
                    ind_arg2
                }.step(ctx)
            },
            Imax(l, r) => {
                let (l_prime, h1) = l.subst(ks, vs, ctx);
                let (r_prime, h2) = r.subst(ks, vs, ctx);
                let ind_arg2 = l_prime.new_imax(r_prime, ctx);
                SubstL::Imax {
                    l,
                    r,
                    l_prime,
                    r_prime,
                    ks,
                    vs,
                    h1,
                    h2,
                    ind_arg1 : self,
                    ind_arg2
                }.step(ctx)                
            },
            Param(n) => match (ks.read(ctx), vs.read(ctx)) {
                (Nil, Nil) => {
                    SubstL::ParamNil {
                        n,
                        ind_arg1 : self,
                        ind_arg2 : ks,
                        ind_arg3 : vs,
                    }.step(ctx)
                }
                (Cons(k, ks_tl), Cons(v, vs_tl)) if self == k => {
                    SubstL::ParamHit {
                        n,
                        v,
                        ks_tl,
                        vs_tl,
                        ind_arg1 : self,
                        ind_arg2 : ks,
                        ind_arg3 : vs,
                    }.step(ctx)
                }
                (Cons(k, ks_tl), Cons(v, vs_tl)) => {
                    let h1 = self == k;
                    let (l_prime, h2) = self.subst(ks_tl, vs_tl, ctx);
                    SubstL::ParamMiss {
                        n,
                        k,
                        v,
                        l_prime,
                        ks_tl,
                        vs_tl,
                        h1,
                        h2,
                        ind_arg1 : self,
                        ind_arg2 : ks,
                        ind_arg3 : vs,
                    }.step(ctx)
                }
                _ => unreachable!("level::subst must get lists of equal length!")
            }
        }
    }

    fn leq_core(
        self,
        other : Self,
        l_h : usize,
        r_h : usize,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (bool, Step<LeqCore<'a>>)  {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, _) if l_h <= r_h => {
                LeqCore::ZAny {
                    r : other,
                    l_h,
                    r_h,
                    h1 : l_h <= r_h,
                    ind_arg1 : self,
                    res : true
                }.step(ctx)
            },
            (_, Zero) if r_h < l_h => {
                LeqCore::AnyZ {
                    l : self,
                    l_h,
                    r_h,
                    h1 : r_h < l_h,
                    ind_arg2 : other,
                    res : false
                }.step(ctx)
            },
            (Param(n1), Param(n2)) => {
                LeqCore::ParamParam {
                    n1,
                    n2,
                    l_h,
                    r_h,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res : ((n1 == n2) && (l_h <= r_h)),
                }.step(ctx)
            },
            (Param(n), Zero) => {
                LeqCore::ParamZero {
                    n,
                    l_h,
                    r_h,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res : false
                }.step(ctx)
            },
            (Zero, Param(n)) => {
                LeqCore::ZeroParam {
                    n,
                    l_h,
                    r_h,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res : l_h <= r_h
                }.step(ctx)
            },
            (Succ(pred), _) => {
                let (res, h1) = pred.leq_core(other, 1 + l_h, r_h, ctx);
                LeqCore::SuccAny {
                    l : pred,
                    r : other,
                    l_h,
                    r_h,
                    b : res,
                    h1,
                    ind_arg1 : self,
                }.step(ctx)
            },
            (_, Succ(pred)) => {
                let (res, h1) = self.leq_core(pred, l_h, 1 + r_h, ctx);
                LeqCore::AnySucc {
                    l : self,
                    r : pred,
                    l_h,
                    r_h,
                    b : res,
                    h1,
                    ind_arg2 : other,
                }.step(ctx)
            },
            (Max(a, b), _) => {
                let (b1, h1) = a.leq_core(other, l_h, r_h, ctx);
                let (b2, h2) = b.leq_core(other, l_h, r_h, ctx);
                let res = b1 && b2;
                LeqCore::MaxAny {
                    a,
                    b,
                    r : other,
                    l_h,
                    r_h,
                    b1,
                    b2,
                    h1,
                    h2,
                    ind_arg1 : self,
                    res
                }.step(ctx)
            },
            (Param(n), Max(x, y)) => {
                let (b1, h1) = self.leq_core(x, l_h, r_h, ctx);
                let (b2, h2) = self.leq_core(y, l_h, r_h, ctx);
                let res = b1 && b2;
                LeqCore::ParamMax {
                    n,
                    x,
                    y,
                    b1,
                    b2,
                    l_h,
                    r_h,
                    h1,
                    h2,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res
                }.step(ctx)
            },
            (Zero, Max(x, y)) => {
                let (b1, h1) = self.leq_core(x, l_h, r_h, ctx);
                let (b2, h2) = self.leq_core(y, l_h, r_h, ctx);
                let res = b1 && b2;
                LeqCore::ZeroMax {
                    x,
                    y,
                    b1,
                    b2,
                    l_h,
                    r_h,
                    h1,
                    h2,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res
                }.step(ctx)
            },
            (Imax(a, b), Imax(x, y)) if a == b && x == y => {
                LeqCore::ImaxCongr {
                    l : a,
                    r : b,
                    l_h,
                    r_h,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    res : true
                }.step(ctx)
            },
            (Imax(a, p), _) if p.is_param(ctx).0 => {
                let n = match p.read(ctx) {
                    Param(n) => n,
                    _ => unreachable!("Checked pattern; leq_core ImaxParamL")
                };

                // ks = [Param(n)]
                let ks = levels!([p], ctx);
                // z_vs = [Zero]
                let z_vs = levels!([Zero.alloc(ctx)], ctx);
                // s_vs = [Succ(Param(n))];
                let succ_vs = levels!([p.new_succ(ctx)], ctx);

                let (l_z, h1) = self.subst(ks, z_vs, ctx);
                let (r_z, h2) = other.subst(ks, z_vs, ctx);
                let (l_z_prime, h3) = l_z.simplify(ctx);
                let (r_z_prime, h4) = r_z.simplify(ctx);

                let (l_succ, h5) = self.subst(ks, succ_vs, ctx);
                let (r_succ, h6) = other.subst(ks, succ_vs, ctx);
                let (l_succ_prime, h7) = l_succ.simplify(ctx);
                let (r_succ_prime, h8) = r_succ.simplify(ctx);
                let (b1, h9) = l_z_prime.leq_core(r_z_prime, l_h, r_h, ctx);
                let (b2, h10) = l_succ_prime.leq_core(r_succ_prime, l_h, r_h, ctx);
                let res = b1 && b2;
                LeqCore::ImaxParamL {
                    n,
                    a,
                    r : other,
                    l_z,
                    r_z,
                    l_z_prime,
                    r_z_prime,
                    l_succ,
                    r_succ,
                    l_succ_prime,
                    r_succ_prime,
                    l_h,
                    r_h,
                    b1,
                    b2,
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
                    ind_arg1 : self,
                    res
                }.step(ctx)
            },
            (_, Imax(x, p)) if p.is_param(ctx).0 => {
                let n = match p.read(ctx) {
                    Param(n) => n,
                    _ => unreachable!("Checked pattern match; LeqCore::ImaxParamR"),
                };

                let ks = levels!([p], ctx);
                let z_vs = levels!([Zero.alloc(ctx)], ctx);
                let succ_vs = levels!([p.new_succ(ctx)], ctx);
                let (l_z, h1) = self.subst(ks, z_vs, ctx);
                let (r_z, h2) = other.subst(ks, z_vs, ctx);
                let (l_z_prime, h3) = l_z.simplify(ctx);
                let (r_z_prime, h4) = r_z.simplify(ctx);
                let (l_succ, h5) = self.subst(ks, succ_vs, ctx);
                let (r_succ, h6) = other.subst(ks, succ_vs, ctx);
                let (l_succ_prime, h7) = l_succ.simplify(ctx);
                let (r_succ_prime, h8) = r_succ.simplify(ctx);
                let (b1, h9) = l_z_prime.leq_core(r_z_prime, l_h, r_h, ctx);
                let (b2, h10) = l_succ_prime.leq_core(r_succ_prime, l_h, r_h, ctx);
                let res = b1 && b2;
                LeqCore::ImaxParamR {
                    n,
                    x,
                    l : self,
                    l_z,
                    r_z,
                    l_z_prime,
                    r_z_prime,
                    l_succ,
                    r_succ,
                    l_succ_prime,
                    r_succ_prime,
                    l_h,
                    r_h,
                    b1,
                    b2,
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
                    ind_arg2 : other,
                    res,
                }.step(ctx)
            },
            (Imax(a, b), _) if b.is_any_max(ctx).0 => match b.read(ctx) {
                Imax(c, d) => {
                    let im_a_d  = <Self>::new_imax(a, d, ctx); 
                    let im_c_d = <Self>::new_imax(c, d, ctx);
                    let new_max = <Self>::new_max(im_a_d, im_c_d, ctx);
                    let (res, h1) = new_max.leq_core(other, l_h, r_h, ctx);
                    LeqCore::ImaxImaxAny {
                        a,
                        c,
                        d,
                        r : other,
                        l_h,
                        r_h,
                        b : res,
                        h1,
                        ind_arg1 : self,
                    }.step(ctx)
                },
                Max(c, d) => {
                    let im_a_c = <Self>::new_imax(a, c, ctx);
                    let im_a_d = <Self>::new_imax(a, d, ctx);
                    let (new_max_prime, h1) = <Self>::new_max(im_a_c, im_a_d, ctx).simplify(ctx);
                    let (res, h2) = new_max_prime.leq_core(other, l_h, r_h, ctx);
                    LeqCore::ImaxMaxAny {
                        a,
                        c,
                        d,
                        r : other,
                        new_max_prime,
                        l_h,
                        r_h,
                        b : res,
                        h1,
                        h2,
                        ind_arg1 : self,
                    }.step(ctx)
                },
                _ => unreachable!("checked pattern : ImaxParamL")
            },
                
            (_, Imax(x, y)) if y.is_any_max(ctx).0 => match y.read(ctx) {
                Imax(j, k) => {
                    let im_x_k = <Self>::new_imax(x, k, ctx);
                    let im_j_k = <Self>::new_imax(j, k, ctx);
                    let new_max = <Self>::new_max(im_x_k, im_j_k, ctx);                    
                    let (res, h1) = self.leq_core(new_max, l_h, r_h, ctx);
                    LeqCore::AnyImaxImax {
                        l : self,
                        x,
                        j,
                        k,
                        l_h,
                        r_h,
                        b : res,
                        h1,
                        ind_arg2 : other,
                    }.step(ctx)
                },
                Max(j, k) => {
                    let im_x_j = <Self>::new_imax(x, j, ctx);
                    let im_x_k = <Self>::new_imax(x, k, ctx);
                    let (new_max_prime, h1) = <Self>::new_max(im_x_j, im_x_k, ctx).simplify(ctx);                    
                    let (res, h2) = self.leq_core(new_max_prime, l_h, r_h, ctx);
                    LeqCore::AnyImaxMax {
                        l : self,
                        x,
                        j,
                        k,
                        new_max_prime,
                        l_h,
                        r_h,
                        b : res,
                        h1,
                        h2,
                        ind_arg2 : other,
                    }.step(ctx)
                },
                _ => unreachable!("checked pattern : ImaxParamR")
            }
            _ => panic!()
        }
    }

    pub fn leq(
        self,
        other : LevelPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<Leq<'a>>) {
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

    pub fn eq_antisymm(
        self,
        other : LevelPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<EqAntisymm<'a>>) {
        let (b1, h1) = self.leq(other, ctx);
        let (b2, h2) = other.leq(self, ctx);
        EqAntisymm::Base {
            l : self,
            r : other,
            b1,
            b2,
            h1,
            h2,
            ind_arg3 : b1 && b2
        }.step(ctx)
    }

    pub fn is_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsZero<'a>>) {
        let (b, h1) = self.leq(Zero.alloc(ctx), ctx);
        IsZero::Base {
            l : self,
            b,
            h1
        }.step(ctx)
    }

    pub fn is_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<IsNonzero<'a>>) {
        let (b, h1) = Zero.alloc(ctx).new_succ(ctx).leq(self, ctx);
        IsNonzero::Base {
            l : self,
            b,
            h1,
        }.step(ctx)
    }

    pub fn maybe_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<MaybeZero<'a>>) {
        let (b, h1) = self.is_nonzero(ctx);
        MaybeZero::Base {
            l : self,
            b,
            h1
        }.step(ctx)
    }

    pub fn maybe_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> (bool, Step<MaybeNonzero<'a>>) {
        let (b, h1) = self.is_zero(ctx);
        MaybeNonzero::Base {
            l : self,
            b,
            h1
        }.step(ctx)
    }
}

impl<'a> LevelsPtr<'a> {
    pub fn params_defined_many(
        self,
        dec_ups : LevelsPtr<'a>,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (bool, Step<ParamsDefinedMany<'a>>) {
        match self.read(ctx) {
            Nil => {
                ParamsDefinedMany::Base {
                    dec_ups,
                    ind_arg1 : self,
                    out : true
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (b1, h1) = tl.params_defined_many(dec_ups, ctx);
                let (b2, h2) = hd.params_defined(dec_ups, ctx);
                let out = b1 && b2;
                ParamsDefinedMany::Step {
                    hd,
                    tl,
                    dec_ups,
                    h1,
                    h2,
                    ind_arg1 : self,
                    out
                }.step(ctx)
            }
        }
    }

    pub fn subst_many(
        self,
        ks : Self,
        vs : Self,
        ctx : &mut impl IsLiveCtx<'a>,
    ) -> (LevelsPtr<'a>, Step<SubstLMany<'a>>) {
        match self.read(ctx) {
            Nil => {
                SubstLMany::Base {
                    ks,
                    vs,
                    ind_arg1 : self,
                }.step(ctx)
            },
            Cons(hd, tl) => {
                let (hd_prime, h1) = hd.subst(ks, vs, ctx);
                let (tl_prime, h2) = tl.subst_many(ks, vs, ctx);
                SubstLMany::Step {
                    hd,
                    hd_prime,
                    tl,
                    tl_prime,
                    ks,
                    vs,
                    ind_arg1 : self,
                    ind_arg2 : Cons(hd_prime, tl_prime).alloc(ctx),
                }.step(ctx)
            }
        }
    }

    pub fn eq_antisymm_many(
        self,
        other : Self,
        ctx : &mut impl IsLiveCtx<'a>
    ) -> (bool, Step<EqAntisymmMany<'a>>) {
        match (self.read(ctx), other.read(ctx)) {
            (Nil, Nil) => {
                EqAntisymmMany::Base {
                    ind_arg1 : self,
                    b : true,
                }.step(ctx)
            },
            (Cons(l, ls), Nil) => {
                EqAntisymmMany::BaseFL {
                    l,
                    ls,
                    ind_arg2 : other,
                    b : false,
                }.step(ctx)
            }
            (Nil, Cons(r, rs)) => {
                EqAntisymmMany::BaseFR {
                    r,
                    rs,
                    ind_arg1 : self,
                    b : false
                }.step(ctx)
            },
            (Cons(l, ls), Cons(r, rs)) => {
                let (b1, h1) = l.eq_antisymm(r, ctx);
                let (b2, h2) = ls.eq_antisymm_many(rs, ctx);
                EqAntisymmMany::Step {
                    l,
                    r,
                    ls,
                    rs,
                    b1,
                    b2,
                    h1,
                    h2,
                    ind_arg1 : self,
                    ind_arg2 : other,
                    b : b1 && b2
                }.step(ctx)
            },
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


