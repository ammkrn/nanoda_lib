use crate::name::{ NamePtr };
use crate::expr::{ Expr::*, ExprPtr };
use crate::levels;
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

impl<'a> Level<'a> {
    pub fn insert_env<'e>(
        self, 
        env : &mut Env<'e>, 
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

    pub fn is_any_max(self, ctx : &impl IsLiveCtx<'a>) -> bool {
        matches!(self.read(ctx), Max(..) | Imax(..))
    }

    pub fn is_param(self, ctx : &impl IsLiveCtx<'a>) -> bool {
        matches!(self.read(ctx), Param(..))
    }

    
    pub fn combining(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> LevelPtr<'a> {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, r) => r.alloc(ctx),
            (l, Zero) => l.alloc(ctx),
            (Succ(l), Succ(r)) => l.combining(r, ctx).new_succ(ctx),
            _ => self.new_max(other, ctx)
        }
    }

    pub fn simplify(self, ctx : &mut impl IsLiveCtx<'a>) -> LevelPtr<'a> {
        match self.read(ctx) {
            Zero => Zero.alloc(ctx),
            p @ Param(..) => p.alloc(ctx),
            Succ(pred) => pred.simplify(ctx).new_succ(ctx),
            Max(l, r) => {
                let l_prime = l.simplify(ctx);
                let r_prime = r.simplify(ctx);
                l_prime.combining(r_prime, ctx)
            },
            Imax(l, r) => {
                let r_prime = r.simplify(ctx);
                match r_prime.read(ctx) {
                    Zero => r_prime,
                    Succ(..) => l.simplify(ctx).combining(r_prime, ctx),
                    _ => l.simplify(ctx).new_imax(r_prime, ctx)
                }
            }
        }
    }    

    
    // for some level `l` and list of params `ps`,
    // assert that :
    // `forall Level::Param(n) \in l, Level::Param(n) \in ps`
    pub fn all_params_defined(self, params : LevelsPtr<'a>, ctx : &impl IsLiveCtx<'a>) -> bool {
        match self.read(ctx) {
            Zero => true,
            Succ(pred) => pred.all_params_defined(params, ctx),
            | Max(lhs, rhs)
            | Imax(lhs, rhs) => lhs.all_params_defined(params, ctx) 
                                && rhs.all_params_defined(params, ctx),
            Param(_) => match params.read(ctx) {
                Nil => false,
                Cons(hd, _) if self == hd => true,
                Cons(_, tl) => self.all_params_defined(tl, ctx)
            }
        }
    }

    pub fn subst(
        self, 
        ks : LevelsPtr<'a>, 
        vs : LevelsPtr<'a>, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> LevelPtr<'a> {
        match self.read(ctx) {
            Zero => Zero.alloc(ctx),
            Succ(pred) => pred.subst(ks, vs, ctx).new_succ(ctx),
            Max(l, r) => {
                let l_prime = l.subst(ks, vs, ctx);
                let r_prime = r.subst(ks, vs, ctx);
                l_prime.new_max(r_prime, ctx)
            },
            Imax(l, r) => {
                let l_prime = l.subst(ks, vs, ctx);
                let r_prime = r.subst(ks, vs, ctx);
                l_prime.new_imax(r_prime, ctx)
            }
            Param(..) => match (ks.read(ctx), vs.read(ctx)) {
                (Cons(k, _), Cons(v, _)) if self == k => v,
                (Cons(_, ks_tl), Cons(_, vs_tl)) => self.subst(ks_tl, vs_tl, ctx),
                (Nil, Nil) => self,
                _ => unreachable!("level::subst must get lists of equal length!")
            }
        }
    }       

    
    
    fn ensure_imax_leq(
        self, 
        lhs : Self,
        rhs : Self,
        diff : isize, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> bool {
        assert!(self.is_param(ctx));
        let self_list = levels!([self], ctx);
        let zero_list = levels!([Zero.alloc(ctx)], ctx);
        let succ_of_list = levels!([self.new_succ(ctx)], ctx);

        let mut closure = |k : LevelsPtr<'a>, v : LevelsPtr<'a>| {
            let lhs_p = lhs.subst(k, v, ctx).simplify(ctx);
            let rhs_p = rhs.subst(k, v, ctx).simplify(ctx);
            lhs_p.leq_core(rhs_p, diff, ctx)
        };

        closure(self_list, zero_list) && closure(self_list, succ_of_list)
    }
    // Important note about this is that a return value of `false` does NOT
    // indicate `greater than`, it just means "L is not less than or equal to R"
    // since there are times where we can't say for sure one way or the other.
    // An example would be (Param(A), Param(X)). Without some extra information
    // (which this function will never receive), there's no way to know whether
    // any particular substitution for A and X will produce a pair such that 
    // L <= R or R <= L   
    fn leq_core(
        self, 
        other : Self, 
        diff : isize, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> bool {
        match (self.read(ctx), other.read(ctx)) {
            (Zero, _) if diff >= 0             => true,
            (_, Zero) if diff < 0              => false,
            (Param(a), Param(x))               => a == x && diff >= 0,
            (Param(..), Zero)                  => false,
            (Zero, Param(..))                  => diff >= 0,

            (Succ(s), _)                       => s.leq_core(other, diff - 1, ctx),
            (_, Succ(s))                       => self.leq_core(s, diff + 1, ctx),

            (Max(a, b), _)                     => a.leq_core(other, diff, ctx) 
                                               && b.leq_core(other, diff, ctx),

            (Param(..), Max(x, y))             => self.leq_core(x, diff, ctx)
                                               || self.leq_core(y, diff, ctx),

            (Zero, Max(x, y))                  => self.leq_core(x, diff, ctx)
                                               || self.leq_core(y, diff, ctx),

            (Imax(a, b), Imax(x, y)) if (a == x) && (b == y) => true,

            (Imax(.., b), _) if b.is_param(ctx)   => b.ensure_imax_leq(self, other, diff, ctx),

            (_, Imax(.., y)) if y.is_param(ctx)   => y.ensure_imax_leq(self, other, diff, ctx),

            (Imax(a, b), _) if b.is_any_max(ctx)  => match b.read(ctx) {
               Imax(x, y) => {

                   let new_lhs = <Self>::new_imax(a, y, ctx); 
                   let new_rhs = <Self>::new_imax(x, y, ctx);
                   let new_max = <Self>::new_max(new_lhs, new_rhs, ctx);
                   new_max.leq_core(other, diff, ctx)
               },
               Max(x, y) => {
                    let new_lhs = <Self>::new_imax(a, x, ctx);
                    let new_rhs = <Self>::new_imax(a, y, ctx);
                    let new_max = <Self>::new_max(new_lhs, new_rhs, ctx).simplify(ctx);
                    new_max.leq_core(other, diff, ctx)
                },
                _ => unreachable!(),
            },

            (_, Imax(x, y)) if y.is_any_max(ctx)  => match y.read(ctx) {
                Imax(j, k) => {
                    let new_lhs = <Self>::new_imax(x, k, ctx);
                    let new_rhs = <Self>::new_imax(j, k, ctx);
                    let new_max = <Self>::new_max(new_lhs, new_rhs, ctx);
                    self.leq_core(new_max, diff, ctx)
                },
                Max(j, k) => {
                    let new_lhs = <Self>::new_imax(x, j, ctx);
                    let new_rhs = <Self>::new_imax(x, k, ctx);
                    let new_max = <Self>::new_max(new_lhs, new_rhs, ctx).simplify(ctx);
                    self.leq_core(new_max, diff, ctx)
                },
                _ => unreachable!(),
            }
            _ => unreachable!()
        }
    }            


    pub fn leq(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        let l_prime = self.simplify(ctx);
        let r_prime = other.simplify(ctx);
        l_prime.leq_core(r_prime, 0, ctx)
    }

    pub fn geq(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        self.eq_antisymm(other, ctx)
        || (!self.leq(other, ctx))
    }

    pub fn eq_antisymm(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        self.leq(other, ctx) 
        && other.leq(self, ctx)
    }        

    // For these inequality predicates, we need to do somewhat goofy
    // looking things because of Imax/Param interaction, where
    // levels can be equal to zero without literally being `Level::Zero`
    pub fn is_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        self.leq(Zero.alloc(ctx), ctx)
    }

    pub fn is_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        Zero.alloc(ctx).new_succ(ctx).leq(self, ctx)
    }

    pub fn maybe_zero(self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        !self.is_nonzero(ctx)
    }

    pub fn maybe_nonzero(self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        !self.is_zero(ctx)
    }

    pub fn use_dep_elim(self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        self.maybe_nonzero(ctx)
    }           

}

impl<'a> LevelsPtr<'a> {
    pub fn subst_many(self, ks : Self, vs : Self, ctx : &mut impl IsLiveCtx<'a>) -> Self {
        match self.read(ctx) {
            Nil => Nil::<Level>.alloc(ctx),
            Cons(hd, tl) => {
                let sink = tl.subst_many(ks, vs, ctx);
                let hd = hd.subst(ks, vs, ctx);
                Cons(hd, sink).alloc(ctx)
            }
        }
    }
    pub fn all_params_defined_many(self, ls : Self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        match self.read(ctx) {
            Nil => true,
            Cons(hd, tl) => hd.all_params_defined(ls, ctx) 
                            && tl.all_params_defined_many(ls, ctx)
        }
    }

    pub fn eq_antisymm_many(self, other : Self, ctx : &mut impl IsLiveCtx<'a>) -> bool {
        match (self.read(ctx), other.read(ctx)) {
            (Cons(hd_l, tl_l), Cons(hd_r, tl_r)) => {
                hd_l.eq_antisymm(hd_r, ctx)
                && tl_l.eq_antisymm_many(tl_r, ctx)
            },
            (Nil, Nil) => true,
            _ => false
        }
    }

    
    pub fn fold_imaxs(self, sink : LevelPtr<'a>, ctx : &mut impl IsLiveCtx<'a>) -> LevelPtr<'a> {
        match self.read(ctx) {
            Nil => sink,
            Cons(hd, tl) => tl.fold_imaxs(hd.new_imax(sink, ctx), ctx)
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
