use std::sync::Arc;
use hashbrown::HashSet;

use crate::name::Name;
use crate::errors;
use crate::utils::{ HasInstantiate };

use InnerLevel::*;




/// `Level` and `InnerLevel` together represent Lean's Sort/Universe level terms.
/// Structurally, they're just trees, with `Level` acting as a reference counted
/// wrapper around `InnerLevel`. Zero and Param values are always leaves;
/// Zero is just Zero, and Param represents a variable by wrapping a `Name` value
/// (like when you see `Sort u` in Lean).
/// Succ is just like nat's succ, with the predecessor it points to as its only child. 
/// `Max` is a node which always has two children, and represents the eventual 
/// maximum of two `Level` values, which we can't always immediately resolve due to
/// the presence of variables (Params). 
/// `IMax` is a `Max` node with one special behavior; any time the right hand branch
/// of an `IMax` resolves to `Zero`, the whole term resolves to `Zero`.
/// This behavior has to do with correctly handling `Prop`, which you can read more
/// about in 'Theorem Proving in Lean'
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Level(Arc<InnerLevel>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum InnerLevel {
    Zero,
    Succ (Level),
    Max  (Level, Level),
    IMax (Level, Level),
    Param(Name),
}


impl<'x> HasInstantiate<(&'x Level, &'x Level)> for Level {
    fn instantiate<I>(&self, substs : I) -> Level
    where I : Iterator<Item = (&'x Level, &'x Level)> + Clone {
        match self.as_ref() {
            Zero => mk_zero(),
            Succ(inner) => mk_succ(inner.instantiate(substs)),
            Max(a, b) => {
                let a_prime = a.instantiate(substs.clone());
                let b_prime = b.instantiate(substs);
                mk_max(a_prime, b_prime)
            },
            IMax(a, b) => {
                let a_prime = a.instantiate(substs.clone());
                let b_prime = b.instantiate(substs);
                mk_imax(a_prime, b_prime)
            },
            Param(..) => {
                substs.clone()
                      .find(|(l, _)| *l == self)
                      .map(|(_, r)| r.clone())
                      .unwrap_or_else(|| self.clone())
            }
        }
    }
}

pub fn mk_zero() -> Level {
    Level(Arc::new(InnerLevel::Zero))
}

pub fn mk_max(lhs : Level, rhs : Level) -> Level {
    Level(Arc::new(Max(lhs, rhs)))
}

pub fn mk_imax(lhs : Level, rhs : Level) -> Level {
    Level(Arc::new(IMax(lhs, rhs)))
}

pub fn mk_imax_refs(lhs : &Level, rhs : &Level) -> Level {
    Level(Arc::new(IMax(lhs.clone(), rhs.clone())))
}

pub fn mk_param(n : impl Into<Name>) -> Level {
    Level(Arc::new(Param(n.into())))
}

pub fn mk_succ(l : Level) -> Level {
    Level(Arc::new(Succ(l)))
}

pub fn is_def_eq_lvls(lhs : &Vec<Level>, rhs : &Vec<Level>) -> bool {
    lhs.iter().zip(rhs.iter()).all(|(l, r)| l.eq_by_antisymm(r))
}


impl Level {
    pub fn get_param_name(&self) -> &Name {
        match self.as_ref() {
            Param(n) => n,
            owise    => errors::err_param_name(line!(), owise)
        }
    }

    pub fn is_param(&self) -> bool {
        match self.as_ref() {
            Param(..) => true,
            _         => false
        }
    }

    pub fn is_any_max(&self) -> bool {
        match self.as_ref() {
            Max(..) | IMax(..) => true,
            _                  => false
        }
    }

    pub fn has_param(&self) -> bool {
        match self.as_ref() {
            Zero => false,
            Succ(inner) => inner.has_param(),
            Max(l, r) | IMax(l, r) => l.has_param() || r.has_param(),
            Param(_) => true
        }
    }




    pub fn get_undef_param(&self, params : &Vec<Level>) -> Option<Level> {
        match self.as_ref() {
            Zero => None,
            Succ(inner) => inner.get_undef_param(params),
            Max(lhs, rhs) | IMax(lhs, rhs) => {
                lhs.get_undef_param(params).or(rhs.get_undef_param(params))
            },
            Param(_) => {
                if !params.contains(self) {
                    return Some(self.clone())
                } else {
                    None
                }
            }
        }
     }

    /// A non-naive way of combining two `Level` values (naive would be just 
    /// creating a Max). gets used in `simplify`.
    pub fn combining(&self, other : &Level) -> Self {
        match (self.as_ref(), other.as_ref()) {
            (Zero, _)              => other.clone(),
            (_, Zero)              => self.clone(),
            (Succ(lhs), Succ(rhs)) => mk_succ(lhs.combining(rhs)),
            _                      => mk_max(self.clone(), other.clone())

        }
    }

    /// Brief simplification procedure mostly aimed at simplifying IMax terms 
    /// (the rule about an IMax with a right hand side of Zero becoming Zero 
    /// is enforced here).
    pub fn simplify(&self) -> Level {
        match self.as_ref() {
            Zero | Param(..) => self.clone(),
            Succ(lvl)        => mk_succ(lvl.simplify()),
            Max(a, b)        => mk_max(a.simplify(), b.simplify()),
            IMax(a, b)       => {
                let b_prime = b.simplify();
                match b_prime.as_ref() {
                    Zero        => mk_zero(), 
                    Succ(..)    => a.simplify().combining(&b_prime),
                    _ => mk_imax(a.simplify(), b_prime)
                }
            }
        }
    }

    /// This is used in `leq_core` to handle the case where one of the levels in question 
    /// is an IMax whose right hand side is some paramter `P`. In light of the 
    /// special behvior of the right hand side of an IMax term, we need to essentially 
    /// do case analysis on our terms before we can say for sure whether lhs <= rhs.
    /// The cases we need to consider are :
    /// 1. `P` will eventually be instantiated as `Zero`
    /// 2. `P` will eventually be instantiated as some non-zero level.
    /// 
    /// So, we create two substitutions, and check that `leq` is true for both.
    ///```pseudo
    /// let (lhs', rhs') = (lhs[Zero/P], rhs[Zero/P])
    /// let (lhs'', rhs'') = (lhs[Succ(P)/P], rhs[Succ(P)/P])
    /// return (lhs' ≤ rhs') && (lhs'' ≤ rhs'')
    ///```
    pub fn ensure_imax_leq(&self, lhs : &Level, rhs : &Level, diff : i32) -> bool {
        assert!(self.is_param());
        let zero_ = mk_zero();
        let succ_of_ = mk_succ(self.clone());

        let closure = |subst : Option<(&Level, &Level)> , left : &Level, right : &Level| {
            let left_prime = left.instantiate(subst.clone().into_iter()).simplify();
            let right_prime = right.instantiate(subst.into_iter()).simplify();
            left_prime.leq_core(&right_prime, diff)
        };

        closure(Some((self, &zero_)), lhs, rhs)
        &&
        closure(Some((self, &succ_of_)), lhs, rhs)
    }

    pub fn is_geq(&self, other : &Level) -> bool {
        if self.eq_by_antisymm(other)  {
            return true
        } else {
            !(self.leq(other))
        }
    }

    /// Essentially just a big analysis of different cases to determine (in the 
    /// presence of variables and IMax's weirdness) whether the left hand side 
    /// is less than or equal to the right hand side (using the ordering specific to 
    /// Lean's sort terms, not the `Ord` instance Rust would use). 
    /// `diff` is just a way of tracking applications of `Succ(x)` as we unroll 
    /// both sides in each recursive call.
    pub fn leq_core(&self, other : &Level, diff : i32) -> bool {

        match (self.as_ref(), other.as_ref()) {
            (Zero, _) if diff >= 0             => true,
            (_, Zero) if diff < 0              => false,
            (Param(a), Param(x))               => a == x && diff >= 0,
            (Param(..), Zero)                  => false,
            (Zero, Param(..))                  => diff >= 0,

            (Succ(s), _)                       => s.leq_core(other, diff - 1),
            (_, Succ(s))                       => self.leq_core(s, diff + 1),

            (Max(a, b), _)                     => a.leq_core(other, diff) 
                                               && b.leq_core(other, diff),

            (Param(..), Max(x, y))             => self.leq_core(x, diff)
                                               || self.leq_core(y, diff),

            (Zero, Max(x, y))                  => self.leq_core(x, diff)
                                               || self.leq_core(y, diff),

            (IMax(a, b), IMax(x, y)) if a == x 
                                     && b == y => true,

            (IMax(.., b), _) if b.is_param()   => b.ensure_imax_leq(self, other, diff),

            (_, IMax(.., y)) if y.is_param()   => y.ensure_imax_leq(self, other, diff),

            (IMax(a, b), _) if b.is_any_max()  => match b.as_ref() {
                IMax(x, y) => {
                    let new_max = mk_max(mk_imax_refs(a, y), 
                                         mk_imax_refs(x, y));
                    Level::leq_core(&new_max, other, diff)
                },

                Max(x, y) => {
                    let new_max = mk_max(mk_imax_refs(a, x), 
                                         mk_imax_refs(a, y)).simplify();
                    Level::leq_core(&new_max, other, diff)

                },
                _ => unreachable!(),
            }

            (_, IMax(x, y)) if y.is_any_max()  => match y.as_ref() {
                IMax(j, k) => {
                    let new_max = mk_max(mk_imax_refs(x, k),
                                         mk_imax_refs(j, k));
                    self.leq_core(&new_max, diff)
                },
                Max(j, k) => {
                    let new_max = mk_max(mk_imax_refs(x, j), 
                                         mk_imax_refs(x, k)).simplify();
                    self.leq_core(&new_max, diff)
                },
                _ => unreachable!(),
            }
            _ => unreachable!()
        }
    }
    
    /// Outward-facing function that uses `leq_core` to determine whether for two 
    /// levels `L1` and `L2`, `L1 <= L2` using Lean's definition of order on 
    /// universes, not Rust's definition of order on `Level` terms.
    pub fn leq(&self, other : &Level) -> bool {
        self.simplify().leq_core(&other.simplify(), 0)
    }

    /// Uses antisymmetry to determine whether two levels are equal (according 
    /// to Lean's rules for sorts)
    ///```pseudo
    ///(x ≤ y ∧ y ≤ x) → x = y
    ///```
    pub fn eq_by_antisymm(&self, other : &Level) -> bool {
        let l1 = self.simplify();
        let l2 = other.simplify();
        
        l1.leq_core(&l2, 0) && l2.leq_core(&l1, 0)
    }


    /// There is no level strictly less than Zero, so for any level `L`, if `L` is 
    /// less than or equal to Zero, it must be that L is equal to Zero.
    ///```pseudo
    /// `∀ (L : Level), (L ≤ Zero) ∧ (¬ ∃ L' : Level, L' < Zero) → L = Zero`
    ///```
    pub fn is_zero(&self) -> bool {
        self.leq(&mk_zero())
    }

    /// for any level `L`, if Succ (Zero) is less than or equal to `L`, it cannot be 
    /// that L is equal to Zero
    ///```pseudo
    /// ∀ (L : Level), S (Zero) ≤ L → L ≠ 0
    ///```
    pub fn is_nonzero(&self) -> bool {
        mk_succ(mk_zero()).leq(self)
    }

    pub fn maybe_zero(&self) -> bool {
        !self.is_nonzero()
    }

    pub fn maybe_nonzero(&self) -> bool {
        !self.is_zero()
    }

    pub fn to_offset(&self) -> (usize, &Level) {
        let (mut succs, mut inner) = (0usize, self);

        while let Succ(x) = inner.as_ref() {
            succs += 1;
            inner = x;
        }

        return (succs, inner)
    }
}


pub fn unique_univ_params<'l, 's>(lvl : &'l Level) -> HashSet<&'l Level> {
    let mut acc = HashSet::with_capacity(40);
    unique_univ_params_core(lvl, &mut acc);
    acc
}

pub fn unique_univ_params_core<'l, 's>(lvl : &'l Level, acc : &'s mut HashSet<&'l Level>) {
    match lvl.as_ref() {
        Zero             => (),
        Succ(lvl)        => unique_univ_params_core(lvl, acc),
        | Max(lhs, rhs)
        | IMax(lhs, rhs) => {
            unique_univ_params_core(lhs, acc);
            unique_univ_params_core(rhs, acc);
        },
        Param(..)        => { 
            acc.insert(lvl); 
        }
    }
}



impl std::convert::AsRef<InnerLevel> for Level {
    fn as_ref(&self) -> &InnerLevel {
        match self {
            Level(x) => x.as_ref()
        }
    }
}

impl From<Arc<InnerLevel>> for Level {
    fn from(x : Arc<InnerLevel>) -> Level {
        Level(x)
    }
}

impl From<InnerLevel> for Level {
    fn from(x : InnerLevel) -> Level {
        Level(Arc::new(x))
    }
}

impl From<&str> for Level {
    fn from(s : &str) -> Level {
        mk_param(s)
    }
}

impl std::fmt::Debug for Level {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.as_ref())
    }
}

impl std::fmt::Debug for InnerLevel {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Zero           => write!(f, "0"),
            Succ(_)        => {
                let outer = Level::from(self.clone());
                let (succs, inner) = outer.to_offset();
                let s = if inner.is_zero() {
                    format!("1 + {}", succs)
                } else {
                    format!("{} + {:?}", succs, inner)
                };

                write!(f, "{}", s)
            }
            Max(lhs, rhs)  => write!(f, "M({:?}, {:?})", lhs, rhs),
            IMax(lhs, rhs) => write!(f, "I({:?}, {:?})", lhs, rhs),
            Param(n)       => write!(f, "{:?}", n)
        }
    }
}


