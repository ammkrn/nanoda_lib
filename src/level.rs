//! Implementation of the `Level` type representing universes
use crate::util::{LevelPtr, LevelsPtr, NamePtr, TcCtx};

pub(crate) const ZERO_HASH: u64 = 283;
pub(crate) const SUCC_HASH: u64 = 541;
pub(crate) const MAX_HASH: u64 = 1091;
pub(crate) const IMAX_HASH: u64 = 1747;
pub(crate) const PARAM_HASH: u64 = 947;
use Level::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level<'a> {
    Zero,
    Succ(LevelPtr<'a>, u64),
    Max(LevelPtr<'a>, LevelPtr<'a>, u64),
    IMax(LevelPtr<'a>, LevelPtr<'a>, u64),
    Param(NamePtr<'a>, u64),
}

impl<'a> Level<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Zero => ZERO_HASH,
            Succ(.., hash) | Max(.., hash) | IMax(.., hash) | Param(.., hash) => *hash,
        }
    }
}

impl<'a> std::hash::Hash for Level<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn level_succs(&self, mut l: LevelPtr<'t>) -> (LevelPtr<'t>, usize) {
        let mut num_succs = 0usize;
        while let Succ(pred, ..) = self.read_level(l) {
            l = pred;
            num_succs += 1;
        }
        (l, num_succs)
    }

    fn combining(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        match self.read_level_pair(l, r) {
            (Zero, _) => r,
            (_, Zero) => l,
            (Succ(l, ..), Succ(r, ..)) => {
                let pred = self.combining(l, r);
                self.succ(pred)
            }
            _ => self.max(l, r),
        }
    }

    pub fn simplify(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        match self.read_level(l) {
            Zero | Param(..) => l,
            Succ(val, ..) => {
                let val = self.simplify(val);
                self.succ(val)
            }
            Max(l, r, ..) => {
                let l = self.simplify(l);
                let r = self.simplify(r);
                self.combining(l, r)
            }
            IMax(l, r, ..) => {
                let r_simp = self.simplify(r);
                match self.read_level(r_simp) {
                    Zero => r_simp,
                    Succ { .. } => {
                        let l_simp = self.simplify(l);
                        self.combining(l_simp, r_simp)
                    }
                    _ => {
                        let l_simp = self.simplify(l);
                        self.imax(l_simp, r_simp)
                    }
                }
            }
        }
    }

    /// returns `true` iff every element in `ls` is a `Param`, and `ls` has no duplicate elements.
    pub(crate) fn no_dupes_all_params(&mut self, ls: LevelsPtr<'t>) -> bool {
        let mut set = crate::util::new_fx_hash_set();
        for l in self.read_levels(ls).iter().copied() {
            match self.read_level(l) {
                Param(..) =>
                    if set.contains(&l) {
                        return false
                    } else {
                        set.insert(l);
                    },
                _ => return false,
            }
        }
        true
    }

    /// Return `uparams [ks |-> vs]` for a list of uparams
    pub fn subst_levels(&mut self, uparams: LevelsPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelsPtr<'t> {
        let out =
            self.read_levels(uparams).clone().iter().copied().map(|l| self.subst_level(l, ks, vs)).collect::<Vec<_>>();
        self.alloc_levels(std::sync::Arc::from(out))
    }

    /// Return `uparam [ks |-> vs]`
    pub fn subst_level(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelPtr<'t> {
        match self.read_level(level) {
            Zero => self.zero(),
            Succ(val, ..) => {
                let val = self.subst_level(val, ks, vs);
                self.succ(val)
            }
            Max(l, r, ..) => {
                let l_prime = self.subst_level(l, ks, vs);
                let r_prime = self.subst_level(r, ks, vs);
                self.max(l_prime, r_prime)
            }
            IMax(l, r, ..) => {
                let l_prime = self.subst_level(l, ks, vs);
                let r_prime = self.subst_level(r, ks, vs);
                self.imax(l_prime, r_prime)
            }
            Param(..) => {
                let (ks, vs) = (self.read_levels(ks), self.read_levels(vs));
                for (k, v) in ks.iter().copied().zip(vs.iter().copied()) {
                    if level == k {
                        return v
                    }
                }
                level
            }
        }
    }

    /// for some level `l` and list of params `ps`, assert that:\
    /// `forall Param(n) e. l, n e. params`
    pub(crate) fn all_uparams_defined(&self, level: LevelPtr<'t>, params: LevelsPtr<'t>) -> bool {
        match self.read_level(level) {
            Zero => true,
            Succ(val, ..) => self.all_uparams_defined(val, params),
            Max(l, r, ..) | IMax(l, r, ..) =>
                self.all_uparams_defined(l, params) && self.all_uparams_defined(r, params),
            Param(..) => self.read_levels(params).iter().copied().any(|x| x == level),
        }
    }

    fn is_any_max(&self, level: LevelPtr<'t>) -> bool { matches!(self.read_level(level), Max(..) | IMax(..)) }

    fn is_param(&self, level: LevelPtr<'t>) -> bool { matches!(self.read_level(level), Param(..)) }

    fn subst_simp(&mut self, level: LevelPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> LevelPtr<'t> {
        let l = self.subst_level(level, ks, vs);
        self.simplify(l)
    }

    /// Test whether `lhs <= rhs` by checking whether it holds regardless of whether
    /// a parameter `p` is zero or non-zero.
    fn leq_imax_by_cases(&mut self, param: LevelPtr<'t>, lhs: LevelPtr<'t>, rhs: LevelPtr<'t>, diff: isize) -> bool {
        let zero = self.zero();
        let one = self.succ(zero);
        let zero_slice = self.alloc_levels_slice(&[zero]);
        let one_slice = self.alloc_levels_slice(&[one]);
        let param_slice = self.alloc_levels_slice(&[param]);

        let lhs_0 = self.subst_simp(lhs, param_slice, zero_slice);
        let rhs_0 = self.subst_simp(rhs, param_slice, zero_slice);
        let lhs_s = self.subst_simp(lhs, param_slice, one_slice);
        let rhs_s = self.subst_simp(rhs, param_slice, one_slice);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    // The more positive it is, the more have been applied ot the right side compared to the left side.
    fn leq_core(&mut self, l_in: LevelPtr<'t>, r_in: LevelPtr<'t>, diff: isize) -> bool {
        match self.read_level_pair(l_in, r_in) {
            (Zero, _) if diff >= 0 => true,
            (_, Zero) if diff < 0 => false,
            (Param(a, ..), Param(x, ..)) => a == x && diff >= 0,
            (Param(..), Zero) => false,
            (Zero, Param { .. }) => diff >= 0,
            (Succ(s, ..), _) => self.leq_core(s, r_in, diff - 1),
            (_, Succ(s, ..)) => self.leq_core(l_in, s, diff + 1),
            (Max(a, b, ..), _) => self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff),
            (Param(..), Max(x, y, ..)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (Zero, Max(x, y, ..)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (IMax(a, b, ..), IMax(x, y, ..)) if (a == x) && (b == y) => true,
            (IMax(_, b, _), _) if self.is_param(b) => self.leq_imax_by_cases(b, l_in, r_in, diff),

            (_, IMax(_, y, _)) if self.is_param(y) => self.leq_imax_by_cases(y, l_in, r_in, diff),

            (IMax(a, b, ..), _) if self.is_any_max(b) => match self.read_level(b) {
                IMax(x, y, ..) => {
                    let new_lhs = self.imax(a, y);
                    let new_rhs = self.imax(x, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                Max(x, y, ..) => {
                    let new_lhs = self.imax(a, x);
                    let new_rhs = self.imax(a, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => panic!(),
            },
            (_, IMax(x, y, ..)) if self.is_any_max(y) => match self.read_level(y) {
                IMax(j, k, ..) => {
                    let new_lhs = self.imax(x, k);
                    let new_rhs = self.imax(j, k);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                Max(j, k, ..) => {
                    let new_lhs = self.imax(x, j);
                    let new_rhs = self.imax(x, k);
                    let new_rhs = self.max(new_lhs, new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    self.leq_core(l_in, new_rhs, diff)
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    pub fn leq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        let l_prime = self.simplify(l);
        let r_prime = self.simplify(r);
        self.leq_core(l_prime, r_prime, 0)
    }

    pub fn eq_antisymm(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool { self.leq(l, r) && self.leq(r, l) }

    pub fn eq_antisymm_many(&mut self, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>) -> bool {
        let xs = self.read_levels(xs).clone();
        let ys = self.read_levels(ys).clone();
        if xs.len() != ys.len() {
            return false
        }
        xs.iter().copied().zip(ys.iter().copied()).all(|(x, y)| self.eq_antisymm(x, y))
    }

    /// Does this list of universe parameters already contain `Param(n)` for some `n : Name`
    ///
    /// Used for generating a unique elim universe in the inductive module
    pub(crate) fn contains_param(&self, uparams: LevelsPtr<'t>, candidate: NamePtr<'t>) -> bool {
        self.read_levels(uparams).iter().copied().any(|lptr| match self.read_level(lptr) {
            Param(n, ..) => n == candidate,
            _ => false,
        })
    }

    /// l <= 0 -> is_zero(l)
    pub fn is_zero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        self.leq(level, zero)
    }

    // 1 <= level -> is_nonzero(level)
    pub fn is_nonzero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        let one = self.succ(zero);
        self.leq(one, level)
    }
}
