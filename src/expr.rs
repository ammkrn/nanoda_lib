//! Implementation of Lean expressions
use crate::util::{BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use Expr::*;
use serde::Deserialize;

pub(crate) const VAR_HASH: u64 = 281;
pub(crate) const SORT_HASH: u64 = 563;
pub(crate) const CONST_HASH: u64 = 1129;
pub(crate) const PROJ_HASH: u64 = 17;
pub(crate) const LAMBDA_HASH: u64 = 431;
pub(crate) const LET_HASH: u64 = 241;
pub(crate) const PI_HASH: u64 = 719;
pub(crate) const APP_HASH: u64 = 233;
pub(crate) const LOCAL_HASH: u64 = 211;
pub(crate) const STRING_LIT_HASH: u64 = 1493;
pub(crate) const NAT_LIT_HASH: u64 = 1583;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NamePtr<'a>,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: usize,
        structure: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    /// A bound variable represented by a deBruijn index.
    Var {
        hash: u64,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Pi {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Lambda {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Let {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_type: ExprPtr<'a>,
        val: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
        nondep: bool
    },
    /// A free variable with binder information, and either a unique
    /// identifier, or a deBruijn level.
    Local {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        id: FVarId,
    },
}

/// Free variable identifiers, which are either unique IDs taken from
/// a monotonically increasing counter, or a deBruijn level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FVarId {
    DbjLevel(u16),
    Unique(u32),
}

impl<'a> Expr<'a> {
    pub(crate) fn get_hash(&self) -> u64 {
        match self {
            Var { hash, .. }
            | Sort { hash, .. }
            | Const { hash, .. }
            | App { hash, .. }
            | Pi { hash, .. }
            | Lambda { hash, .. }
            | Let { hash, .. }
            | Local { hash, .. }
            | StringLit { hash, .. }
            | NatLit { hash, .. }
            | Proj { hash, .. } => *hash,
        }
    }
}
impl<'a> std::hash::Hash for Expr<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

/// The style of this binder (in Lean's vernacular, the brackets used to write it).
/// `(_ : _)` for default, `{_ : _}` for implicit, `{{_ : _}}` for strict implicit,
/// and `[_ : _]` for instance implicit.
///
/// These are only used by the pretty printer, and do not change the behavior of
/// type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum BinderStyle {
    #[serde(rename = "default")]
    Default,
    #[serde(rename = "implicit")]
    Implicit,
    #[serde(rename = "strictImplicit")]
    StrictImplicit,
    #[serde(rename = "instImplicit")]
    InstanceImplicit,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn inst_forall_params(&mut self, mut e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for _ in 0..n {
            if let Pi { body, .. } = self.read_expr(e) {
                e = body
            } else {
                panic!()
            }
        }
        self.inst(e, &all_args[0..n])
    }

    /// Instantiate `e` with the substitutions in `substs`
    pub fn inst(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        self.expr_cache.inst_cache.clear();
        self.inst_aux(e, substs, 0)
    }

    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if self.num_loose_bvars(e) <= offset {
            e
        } else if let Some(cached) = self.expr_cache.inst_cache.get(&(e, offset)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                // These expressions should be unreachable since they return `n_loose_bvars() == 0`
                Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)
                }
                App { fun, arg, .. } => {
                    let fun = self.inst_aux(fun, substs, offset);
                    let arg = self.inst_aux(arg, substs, offset);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let val = self.inst_aux(val, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.inst_aux(structure, substs, offset);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.inst_cache.insert((e, offset), calcd);
            calcd
        }
    }

    /// From `e[x_1..x_n/v_1..v_n]`, abstract and re-inst, creating `e[y_1..y_n/v_1..v_n]`.
    pub(crate) fn replace_params(
        &mut self,
        e: ExprPtr<'t>,
        ingoing: &[ExprPtr<'t>],
        outgoing: &[ExprPtr<'t>],
    ) -> ExprPtr<'t> {
        let e = self.abstr(e, outgoing);
        self.inst(e, ingoing)
    }

    /// Abstraction with deBruijn levels instead of unique identifiers.
    fn abstr_aux_levels(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache_levels.get(&(e, start_pos, num_open_binders)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { id: FVarId::DbjLevel(serial), .. } =>
                    if serial < start_pos {
                        e
                    } else {
                        self.fvar_to_bvar(num_open_binders, serial)
                    },
                Local { id: FVarId::Unique(..), .. } => e,
                App { fun, arg, .. } => {
                    let fun = self.abstr_aux_levels(fun, start_pos, num_open_binders);
                    let arg = self.abstr_aux_levels(arg, start_pos, num_open_binders);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let val = self.abstr_aux_levels(val, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.abstr_aux_levels(structure, start_pos, num_open_binders);
                    self.mk_proj(ty_name, idx, structure)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };
            self.expr_cache.abstr_cache_levels.insert((e, start_pos, num_open_binders), calcd);
            calcd
        }
    }

    pub fn abstr_levels(&mut self, e: ExprPtr<'t>, start_pos: u16) -> ExprPtr<'t> {
        self.expr_cache.abstr_cache_levels.clear();
        self.abstr_aux_levels(e, start_pos, self.dbj_level_counter)
    }

    fn abstr_aux(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache.get(&(e, offset)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { .. } =>
                    locals.iter().rev().position(|x| *x == e).map(|pos| self.mk_var(pos as u16 + offset)).unwrap_or(e),
                App { fun, arg, .. } => {
                    let fun = self.abstr_aux(fun, locals, offset);
                    let arg = self.abstr_aux(arg, locals, offset);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let val = self.abstr_aux(val, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.abstr_aux(structure, locals, offset);
                    self.mk_proj(ty_name, idx, structure)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };

            self.expr_cache.abstr_cache.insert((e, offset), calcd);
            calcd
        }
    }

    /// Abstraction of unique identifiers; replaces free variables with the appropriate
    /// bound variable, if the free variable is in `locals`.
    pub fn abstr(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        self.expr_cache.abstr_cache.clear();
        self.abstr_aux(e, locals, 0u16)
    }

    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | NatLit { .. } | StringLit { .. } => e,
                Sort { level, .. } => {
                    let level = self.subst_level(level, ks, vs);
                    self.mk_sort(level)
                }
                Const { name, levels, .. } => {
                    let levels = self.subst_levels(levels, ks, vs);
                    self.mk_const(name, levels)
                }
                App { fun, arg, .. } => {
                    let fun = self.subst_aux(fun, ks, vs);
                    let arg = self.subst_aux(arg, ks, vs);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let val = self.subst_aux(val, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                // Level subst is only used in const inference, and when unfolding definitions;
                // in both cases you're substituting in expressions that were just pulled out of the
                // environment, so they should have no locals.
                Local { .. } => panic!("level substitution should not find locals"),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.subst_aux(structure, ks, vs);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.subst_cache.insert((e, ks, vs), r);
            r
        }
    }

    pub fn subst_expr_levels(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.dsubst_cache.get(&(e, ks, vs)).copied() {
            return cached
        }
        self.expr_cache.subst_cache.clear();
        let out = self.subst_aux(e, ks, vs);
        self.expr_cache.dsubst_cache.insert((e, ks, vs), out);
        out
    }

    pub(crate) fn subst_declar_info_levels(
        &mut self,
        info: crate::env::DeclarInfo<'t>,
        in_vals: LevelsPtr<'t>,
    ) -> ExprPtr<'t> {
        self.subst_expr_levels(info.ty, info.uparams, in_vals)
    }

    pub fn num_args(&self, e: ExprPtr<'t>) -> usize {
        let (mut cursor, mut num_args) = (e, 0);
        while let App { fun, .. } = self.read_expr(cursor) {
            cursor = fun;
            num_args += 1;
        }
        num_args
    }

    /// From `f a_0 .. a_N`, return `f`
    pub fn unfold_apps_fun(&self, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let App { fun, .. } = self.read_expr(e) {
            e = fun;
        }
        e
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`
    pub fn unfold_apps(&self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::new();
        loop {
            match self.read_expr(e) {
                App { fun, arg, .. } => {
                    e = fun;
                    args.push(arg);
                },
                _ => break
            }
        }
        args.reverse();
        (e, args)
    }
    
    /// If this is a const application, return (Const {..}, name, levels, args)
    pub fn unfold_const_apps(
        &self,
        e: ExprPtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>)> {
        let (f, args) = self.unfold_apps(e);
        match self.read_expr(f) {
            Const { name, levels, .. } => Some((f, name, levels, args)),
            _ => None,
        }
    }
    /// If this is an application of `Const(name, levels)`, return `(name, levels)`
    pub fn try_const_info(&self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>)> {
        match self.read_expr(e) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None,
        }
    }

    pub(crate) fn unfold_apps_stack(&self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::new();
        while let App { fun, arg, .. } = self.read_expr(e) {
            args.push(arg);
            e = fun;
        }
        (e, args)
    }

    pub fn foldl_apps(&mut self, mut fun: ExprPtr<'t>, args: impl Iterator<Item = ExprPtr<'t>>) -> ExprPtr<'t> {
        for arg in args {
            fun = self.mk_app(fun, arg);
        }
        fun
    }

    pub(crate) fn abstr_pis<I>(&mut self, mut binders: I, mut body: ExprPtr<'t>) -> ExprPtr<'t>
    where
        I: Iterator<Item = ExprPtr<'t>> + DoubleEndedIterator, {
        while let Some(local) = binders.next_back() {
            body = self.abstr_pi(local, body)
        }
        body
    }

    pub(crate) fn abstr_pi(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply pi with non-local domain type"),
        }
    }

    pub(crate) fn apply_lambda(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply lambda with non-local domain type"),
        }
    }

    pub(crate) fn is_nat_zero(&mut self, e: ExprPtr<'t>) -> bool {
        match self.read_expr(e) {
            Const { .. } => e == self.c_nat_zero(),
            NatLit { ptr, .. } => self.read_bignum(ptr).is_zero(),
            _ => false,
        }
    }

    pub(crate) fn pred_of_nat_succ(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        match self.read_expr(e) {
            App { fun, arg, .. } if fun == self.c_nat_succ() => Some(arg),
            NatLit { ptr, .. } => {
                let n = self.read_bignum(ptr);
                if n > BigUint::zero() {
                    Some(self.mk_nat_lit_quick(n - 1u8))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Used in iota reduction (`reduce_rec`) to turn a bignum
    /// either `Nat.zero`, or `App (Nat.succ) (bignum - 1)`; in order to do iota reduction,
    /// we need to know what constructor the major premise comes from.
    pub(crate) fn nat_lit_to_constructor(&mut self, n: BigUintPtr<'t>) -> ExprPtr<'t> {
        assert!(self.export_file.config.nat_extension);
        let n = self.read_bignum(n);
        if n.is_zero() {
            self.c_nat_zero()
        } else {
            let pred = self.alloc_bignum(core::ops::Sub::sub(n, 1u8));
            let pred = self.mk_nat_lit(pred);
            let succ_c = self.c_nat_succ();
            self.mk_app(succ_c, pred)
        }
    }
    
    /// Return `true` iff `e` is an application of `@eagerReduce A a`
    pub(crate) fn is_eager_reduce_app(&self, e: ExprPtr<'t>) -> bool {
        if let App {fun, ..} = self.read_expr(e) {
            if let App {fun, ..} = self.read_expr(fun) {
                if let Const {name, ..} = self.read_expr(fun) {
                    return self.export_file.name_cache.eager_reduce == Some(name)
                }
            }
        }
        false
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        assert!(self.export_file.config.string_extension);
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        // Const(Char, [])
        let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(self.export_file.name_cache.list_nil?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let mut out = c_list_nil_char;
        for c in self.read_string(s).clone().chars().rev() {
            let bignum = self.alloc_bignum(BigUint::from(c as u32));
            let bignum = self.mk_nat_lit(bignum);
            // Char.ofNat (c as u32)
            let x = self.mk_app(c_char_of_nat, bignum);
            // List.cons (Char.ofNat u32)
            let y = self.mk_app(c_list_cons_char, x);
            // (List.cons (Char.ofNat u32)) xs
            out = self.mk_app(y, out);
        }
        let string_of_list_const = self.mk_const(self.export_file.name_cache.string_of_list?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }

    /// If `e` is a NatLit, or `Const Nat.zero []`, return the appropriate Bignum.
    pub(crate) fn get_bignum_from_expr(&mut self, e: ExprPtr<'t>) -> Option<BigUint> {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            Some(self.read_bignum(ptr))
        } else if e == self.c_nat_zero() {
            Some(BigUint::zero())
        } else {
            None
        }
    }

    /// Return the expression representing either `true` or `false`
    pub(crate) fn bool_to_expr(&mut self, b: bool) -> Option<ExprPtr<'t>> {
        if b {
            self.c_bool_true()
        } else {
            self.c_bool_false()
        }
    }

    pub(crate) fn c_bool_true(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_true?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_bool_false(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_false.unwrap();
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_nat_zero(&mut self) -> ExprPtr<'t> {
        let n = self.export_file.name_cache.nat_zero.unwrap();
        let levels = self.alloc_levels_slice(&[]);
        self.mk_const(n, levels)
    }

    pub(crate) fn c_nat_succ(&mut self) -> ExprPtr<'t> {
        let n = self.export_file.name_cache.nat_succ.unwrap();
        let levels = self.alloc_levels_slice(&[]);
        self.mk_const(n, levels)
    }

    /// Make `Const("Nat", [])`
    pub(crate) fn nat_type(&mut self) -> ExprPtr<'t> {
        let n = self.export_file.name_cache.nat.unwrap();
        let levels = self.alloc_levels_slice(&[]);
        self.mk_const(n, levels)
    }

    /// Make `Const("String", [])`
    pub(crate) fn string_type(&mut self) -> ExprPtr<'t> {
        let n = self.export_file.name_cache.string.unwrap();
        let levels = self.alloc_levels_slice(&[]);
        self.mk_const(n, levels)
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(fun (a b c) => e)`
    pub(crate) fn abstr_lambda_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.apply_lambda(*binder, e);
            binders = tl;
        }
        e
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(Pi (a b c) => e)`
    pub(crate) fn abstr_pi_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.abstr_pi(*binder, e);
            binders = tl;
        }
        e
    }

    pub(crate) fn find_const<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg, .. } => self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache) || self.find_const_aux(body, pred, cache),
                Let { binder_type, val, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache),
                Local { binder_type, .. } => self.find_const_aux(binder_type, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&self, mut e: ExprPtr<'t>) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.read_expr(e) {
            size += 1;
            e = body;
        }
        size
    }

    /// Is this expression `Sort(Level::Zero)`?
    pub(crate) fn prop(&mut self) -> ExprPtr<'t> { self.mk_sort(self.zero()) }
}

impl<'t> Expr<'t> {
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self) -> u16 {
        match self {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => dbj_idx + 1,
            App { num_loose_bvars, .. }
            | Pi { num_loose_bvars, .. }
            | Lambda { num_loose_bvars, .. }
            | Let { num_loose_bvars, .. }
            | Proj { num_loose_bvars, .. } => *num_loose_bvars,
        }
    }

    pub(crate) fn has_fvars(&self) -> bool {
        match self {
            Local { .. } => true,
            Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => false,
            App { has_fvars, .. }
            | Pi { has_fvars, .. }
            | Lambda { has_fvars, .. }
            | Let { has_fvars, .. }
            | Proj { has_fvars, .. } => *has_fvars,
        }
    }
}
impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> u16 { self.read_expr(e).num_loose_bvars() }

    pub(crate) fn has_fvars(&self, e: ExprPtr<'t>) -> bool { self.read_expr(e).has_fvars() }
}
