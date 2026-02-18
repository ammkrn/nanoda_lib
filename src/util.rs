use crate::env::{DeclarMap, Env, NotationMap, EnvLimit};
use crate::expr::{BinderStyle, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::pretty_printer::{PpOptions, PrettyPrinter};
use crate::tc::TypeChecker;
use crate::union_find::UnionFind;
use crate::unique_hasher::UniqueHasher;
use indexmap::{IndexMap, IndexSet};
use num_bigint::BigUint;
use num_traits::{ Pow, identities::Zero };
use num_integer::Integer;
use rustc_hash::FxHasher;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::OpenOptions;
use std::hash::BuildHasherDefault;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use serde::Deserialize;

pub(crate) const fn default_true() -> bool { true }

pub(crate) type UniqueIndexSet<A> = IndexSet<A, BuildHasherDefault<UniqueHasher>>;
pub(crate) type FxIndexSet<A> = IndexSet<A, BuildHasherDefault<FxHasher>>;
pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;
pub(crate) type UniqueHashMap<K, V> = HashMap<K, V, BuildHasherDefault<UniqueHasher>>;

/// An integer pointer to a kernel item, which can be in either the export file's
/// persistent dag, or the type checking context's temporary dag. The integer pointer
/// is currently 32 bits, which comfortably accommodates mathlib.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(packed)]
pub struct Ptr<A> {
    /// The index in the appropriate dag at which this element sits.
    pub(crate) idx: u32,
    /// The dag this pointer points to; the persistent dag in the export file,
    /// or the temporary dag in the type checker context.
    pub(crate) dag_marker: DagMarker,
    pub(crate) ph: PhantomData<A>,
}

const HIGH_MASK: u64 = 1 << 63;

impl<A> Ptr<A> {
    pub(crate) fn from(dag_marker: DagMarker, idx: usize) -> Self {
        Self { idx: u32::try_from(idx).unwrap(), dag_marker, ph: PhantomData }
    }

    pub(crate) fn idx(&self) -> usize { self.idx as usize }

    pub(crate) fn dag_marker(&self) -> DagMarker { self.dag_marker }

    pub(crate) fn get_hash(&self) -> u64 {
        if self.dag_marker == DagMarker::ExportFile {
            self.idx as u64
        } else {
            HIGH_MASK | (self.idx as u64)
        }
    }
}

impl<A> std::hash::Hash for Ptr<A> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DagMarker {
    ExportFile,
    TcCtx,
}

pub(crate) type CowStr<'a> = Cow<'a, str>;
pub type StringPtr<'a> = Ptr<&'a CowStr<'a>>;
pub type LevelsPtr<'a> = Ptr<&'a Arc<[LevelPtr<'a>]>>;
pub type NamePtr<'a> = Ptr<&'a Name<'a>>;
pub type LevelPtr<'a> = Ptr<&'a Level<'a>>;
pub type ExprPtr<'a> = Ptr<&'a Expr<'a>>;
pub type BigUintPtr<'a> = Ptr<&'a BigUint>;

pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> { FxHashMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> { FxHashSet::with_hasher(Default::default()) }

pub(crate) fn new_fx_index_set<K>() -> FxIndexSet<K> { FxIndexSet::with_hasher(Default::default()) }
pub(crate) fn new_unique_index_set<K>() -> UniqueIndexSet<K> { UniqueIndexSet::with_hasher(Default::default()) }

pub(crate) fn new_unique_hash_map<K, V>() -> UniqueHashMap<K, V> { UniqueHashMap::with_hasher(Default::default()) }

/// Convenience macro for creating a 64 bit hash.
#[macro_export]
macro_rules! hash64 {
    ( $( $x:expr ),* ) => {
        {
            use std::hash::{ Hash, Hasher };
            let mut hasher = rustc_hash::FxHasher::default();
            $(
                ($x).hash(&mut hasher);
            )*
            hasher.finish()
        }
    };
}

/// The implementation of natural number subtraction used in the kernel extension
/// for nat literals.
///
/// This is different from the subtraction defined for `BigUint` in that we saturate
/// at zero if y > x
pub(crate) fn nat_sub(x: BigUint, y: BigUint) -> BigUint {
    if y > x {
        BigUint::zero()
    } else {
        x - y
    }
}

/// The implementation of natural number division used in the kernel extension
/// for nat literals.
///
/// This is different from the division defined for `BigUint` in that division
/// by zero is an error for `BigUint`, but in Lean, it returns 0.
pub(crate) fn nat_div(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        BigUint::zero()
    } else {
        x / y
    }
}

/// The implementation of natural number mod used in the kernel extension
/// for nat literals.
pub(crate) fn nat_mod(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        x
    } else {
        x % y
    }
}

pub(crate) fn nat_gcd(x: &BigUint, y: &BigUint) -> BigUint {
    x.gcd(y)
}

pub(crate) fn nat_xor(x: &BigUint, y: &BigUint) -> BigUint {
    x ^ y
}

pub(crate) fn nat_shl(x: BigUint, y: BigUint) -> BigUint {
    x * BigUint::from(2u8).pow(y)
}

pub(crate) fn nat_shr(x: BigUint, y: BigUint) -> BigUint {
    x / BigUint::from(2u8).pow(y)
}

pub(crate) fn nat_land(x: BigUint, y: BigUint) -> BigUint {
    x & y
}
pub(crate) fn nat_lor(x: BigUint, y: BigUint) -> BigUint {
    x | y
}

pub struct ExprCache<'t> {
    /// Caches (e, offset) |-> output for instantiation. This cache is reset
    /// before every new call to `inst`, so there's no need to cache the sequence
    /// of substitutions.
    pub(crate) inst_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// Caches (e, ks, vs) |-> output for level substitution.
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) dsubst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    /// Caches (e, offset) |-> output for abstraction (re-binding free variables).
    /// This cache is reset before every new call to `inst`, so there's no need to
    /// cache the sequence of free variables.
    pub(crate) abstr_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// A cache for (expr, starting deBruijn level, current deBruijn level)
    pub(crate) abstr_cache_levels: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
}

impl<'t> ExprCache<'t> {
    fn new() -> Self {
        Self {
            inst_cache: new_fx_hash_map(),
            abstr_cache: new_fx_hash_map(),
            subst_cache: new_fx_hash_map(),
            dsubst_cache: new_fx_hash_map(),
            abstr_cache_levels: new_fx_hash_map(),
        }
    }
}

pub struct ExportFile<'p> {
    /// The underlying storage for `Name`, `Level`, and `Expr` items (and Strings).
    pub(crate) dag: LeanDag<'p>,
    /// Declarations from the export file
    pub declars: DeclarMap<'p>,
    /// Notations from the export file
    pub notations: NotationMap<'p>,
    /// Cached names for convenience (`Quot`, `Nat`, etc.)
    pub name_cache: NameCache<'p>,
    pub config: Config,
    // Information used for setting EnvLimit during inductive checking.
    pub mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>
}

impl<'p> ExportFile<'p> {
    pub fn new_env(&self, env_limit: EnvLimit<'p>) -> Env<'_, '_> { Env::new(&self.declars, &self.notations, env_limit) }

    pub fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut TcCtx<'_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        f(&mut ctx)
    }

    pub fn with_tc<F, A>(&self, env_limit: EnvLimit, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env(env_limit);
        let mut tc = TypeChecker::new(&mut ctx, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env(EnvLimit::ByName(d.name));
        let mut tc = TypeChecker::new(&mut ctx, &env, Some(d));
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx| ctx.with_pp(f))
    }
}

/// A structure representing the memory context used for an individual `TypeChecker`.
pub struct TcCtx<'t, 'p> {
    //anchor: PhantomData<&'t AnchorZst>,
    /// Each type checker's context shares an immutable reference to the structured contents of
    /// the export file, and some additional information taken from the export file.
    pub(crate) export_file: &'t ExportFile<'p>,
    /// The underlying storage for temporary `Name`, `Level`, and `Expr`` items created while
    /// type checking a declaration. These are dropped once the declaration is verified, since
    /// they are no longer needed.
    pub(crate) dag: &'t mut LeanDag<'t>,
    /// Non-monotonic counter showing the current deBruijn level (which is also the number
    /// of binders that are open above us). When a binder is opened and traversed under, this
    /// counter is incremented. When the binder is closed again, this counter is decremented.
    pub(crate) dbj_level_counter: u16,
    /// Monotonically increasing counter for unique free variables. Any two free variables created
    /// with the `mk_unique` constructor are unique within their `(ExportFile, TcCtx)` pair.
    pub(crate) unique_counter: u32,
    /// A cache for instantiation, free variable abstraction, and level substitution
    pub(crate) expr_cache: ExprCache<'t>,
    pub(crate) eager_mode: bool
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, tdag: &'t mut LeanDag<'t>) -> Self {
        Self { 
            export_file,
            dag: tdag,
            dbj_level_counter: 0u16,
            unique_counter: 0u32,
            expr_cache: ExprCache::new(),
            eager_mode: false
        }
    }

    pub fn with_tc<F, A>(&mut self, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = self.export_file.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(&mut self, env_ext: &'x DeclarMap<'t>, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = crate::env::Env::new_w_temp_ext(&self.export_file.declars, Some(env_ext), &self.export_file.notations, env_limit);
        let mut tc = TypeChecker::new(self, &env, None);
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, 't, 'p>) -> A, {
        f(&mut PrettyPrinter::new(self))
    }

    pub fn read_name(&self, p: NamePtr<'t>) -> Name<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.names.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.names.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_name_pr(&self, p: NamePtr<'t>, q: NamePtr<'t>) -> (Name<'t>, Name<'t>) {
        (self.read_name(p), self.read_name(q))
    }

    pub fn read_level(&self, p: LevelPtr<'t>) -> Level<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.levels.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.levels.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_level_pair(&self, a: LevelPtr<'t>, x: LevelPtr<'t>) -> (Level<'t>, Level<'t>) {
        (self.read_level(a), self.read_level(x))
    }

    pub fn read_expr(&self, p: ExprPtr<'t>) -> Expr<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.exprs.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.exprs.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_expr_pair(&self, a: ExprPtr<'t>, x: ExprPtr<'t>) -> (Expr<'t>, Expr<'t>) {
        (self.read_expr(a), self.read_expr(x))
    }

    pub fn read_string(&self, p: StringPtr<'t>) -> &CowStr<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.strings.get_index(p.idx()).unwrap(),
            DagMarker::TcCtx => self.dag.strings.get_index(p.idx()).unwrap(),
        }
    }

    pub fn read_bignum(&self, p: BigUintPtr<'t>) -> BigUint {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.bignums.get_index(p.idx()).cloned().unwrap(),
            DagMarker::TcCtx => self.dag.bignums.get_index(p.idx()).cloned().unwrap(),
        }
    }

    pub fn read_levels(&self, p: LevelsPtr<'t>) -> Arc<[LevelPtr<'t>]> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.uparams.get_index(p.idx()).cloned().unwrap(),
            DagMarker::TcCtx => self.dag.uparams.get_index(p.idx()).cloned().unwrap(),
        }
    }

    /// Store a `Name`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(idx) = self.export_file.dag.names.get_index_of(&n) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.names.insert_full(n).0)
        }
    }

    /// Store a `Level`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(idx) = self.export_file.dag.levels.get_index_of(&l) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.levels.insert_full(l).0)
        }
    }

    /// Store an `Expr`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(idx) = self.export_file.dag.exprs.get_index_of(&e) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.exprs.insert_full(e).0)
        }
    }

    /// Store a string (a `CowStr`), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub(crate) fn alloc_string(&mut self, s: CowStr<'t>) -> StringPtr<'t> {
        if let Some(idx) = self.export_file.dag.strings.get_index_of(&s) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.strings.insert_full(s).0)
        }
    }

    /// Store a `BigUint` (a bignum), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    ///
    /// Used for Nat literals.
    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> BigUintPtr<'t> {
        if let Some(idx) = self.export_file.dag.bignums.get_index_of(&n) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.bignums.insert_full(n).0)
        }
    }

    /// Store a sequence of `Level` items, getting back a pointer to the allocated sequence.
    /// If the sequence was already stored, return a pointer to the previously inserted sequence.
    /// Checks the longer-lived storage first.
    pub fn alloc_levels(&mut self, ls: Arc<[LevelPtr<'t>]>) -> LevelsPtr<'t> {
        if let Some(idx) = self.export_file.dag.uparams.get_index_of(&ls) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.uparams.insert_full(ls).0)
        }
    }

    /// Store a sequence of `Level` items, but check whether the sequence has previously been allocated
    /// first, by probing with a slice.
    pub fn alloc_levels_slice(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(idx) = self.export_file.dag.uparams.get_index_of(ls) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else if let Some(idx) = self.dag.uparams.get_index_of(ls) {
            Ptr::from(DagMarker::TcCtx, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.uparams.insert_full(Arc::from(ls)).0)
        }
    }

    /// A constructor for the anonymous name.
    pub fn anonymous(&self) -> NamePtr<'t> { self.export_file.dag.anonymous() }

    pub fn str(&mut self, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> NamePtr<'t> {
        let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
        self.alloc_name(Name::Str(pfx, sfx, hash))
    }

    pub fn str1_owned(&mut self, s: String) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Owned(s));
        self.str(anon, s)
    }

    pub fn str1(&mut self, s: &'static str) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Borrowed(s));
        self.str(anon, s)
    }

    pub fn str2(&mut self, s1: &'static str, s2: &'static str) -> NamePtr<'t> {
        let s1 = self.alloc_string(CowStr::Borrowed(s1));
        let s2 = self.alloc_string(CowStr::Borrowed(s2));
        let n = self.anonymous();
        let n = self.str(n, s1);
        self.str(n, s2)
    }

    pub fn zero(&self) -> LevelPtr<'t> { self.export_file.dag.zero() }

    pub fn num(&mut self, pfx: NamePtr<'t>, sfx: u64) -> NamePtr<'t> {
        let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
        self.alloc_name(Name::Num(pfx, sfx, hash))
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::SUCC_HASH, l);
        self.alloc_level(Level::Succ(l, hash))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::MAX_HASH, l, r);
        self.alloc_level(Level::Max(l, r, hash))
    }
    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::IMAX_HASH, l, r);
        self.alloc_level(Level::IMax(l, r, hash))
    }
    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::PARAM_HASH, n);
        self.alloc_level(Level::Param(n, hash))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
        self.alloc_expr(Expr::Var { dbj_idx, hash })
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::SORT_HASH, level);
        self.alloc_expr(Expr::Sort { level, hash })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::CONST_HASH, name, levels);
        self.alloc_expr(Expr::Const { name, levels, hash })
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::APP_HASH, fun, arg);
        let num_loose_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
        let has_fvars = self.has_fvars(fun) || self.has_fvars(arg);
        self.alloc_expr(Expr::App { fun, arg, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_lambda(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
        let num_loose_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(body);
        self.alloc_expr(Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_pi(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
        let num_loose_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(body);
        self.alloc_expr(Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
        let num_loose_bvars = self
            .num_loose_bvars(binder_type)
            .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
        self.alloc_expr(Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep })
    }

    pub fn mk_proj(&mut self, ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
        let num_loose_bvars = self.num_loose_bvars(structure);
        let has_fvars = self.has_fvars(structure);
        self.alloc_expr(Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
        self.alloc_expr(Expr::StringLit { ptr: string_ptr, hash })
    }

    pub fn mk_string_lit_quick(&mut self, s: CowStr<'t>) -> ExprPtr<'t> {
        let string_ptr = self.alloc_string(s);
        self.mk_string_lit(string_ptr)
    }

    pub fn mk_nat_lit(&mut self, num_ptr: BigUintPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
        self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash })
    }

    /// Shortcut to make an `Expr::NatLit` directly from a `BigUint`, rather than
    /// going `alloc_bignum` and `mk_nat_lit`
    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> ExprPtr<'t> {
        let num_ptr = self.alloc_bignum(n);
        self.mk_nat_lit(num_ptr)
    }

    /// Construct a free variable expression representing a deBruijn level, and
    /// increment the context's counter.
    pub fn mk_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let level = self.dbj_level_counter;
        self.dbj_level_counter += 1;
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// Construct a free variable expression representing a deBruijn level, reusing
    /// a particular level counter, and without incrementing the context's counter for
    /// open binders.
    pub fn remake_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        level: u16,
    ) -> ExprPtr<'t> {
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// Construct a free variable with a unique ID, incrementing the monotonic counter
    /// for unique free variable identifiers.
    pub fn mk_unique(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let unique_id = self.unique_counter;
        self.unique_counter += 1;
        let id = FVarId::Unique(unique_id);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// "replace" a free variable when closing a binder, decrementing the deBruijn level
    /// counter, so that level can be reused as appropriate.
    pub(crate) fn replace_dbj_level(&mut self, e: ExprPtr<'t>) {
        match self.read_expr(e) {
            Expr::Local { id: FVarId::DbjLevel(level), .. } => {
                debug_assert_eq!(level + 1, self.dbj_level_counter);
                self.dbj_level_counter -= 1;
            }
            _ => panic!("replace_dbj_level didn't get a Local, got {:?}", self.debug_print(e)),
        }
    }

    /// Convert the deBruijn level of a free variable to a deBruijn index for a bound
    /// variable. This is the same thing as asking "if this element is the `nth` element
    /// when counting from the front of a sequence of length `m`, what is its position
    /// when counting from the back?"
    pub(crate) fn fvar_to_bvar(&mut self, num_open_binders: u16, dbj_level: u16) -> ExprPtr<'t> {
        self.mk_var((num_open_binders - dbj_level) - 1)
    }
}

#[derive(Debug)]
pub struct LeanDag<'a> {
    pub names: UniqueIndexSet<Name<'a>>,
    pub levels: UniqueIndexSet<Level<'a>>,
    pub exprs: UniqueIndexSet<Expr<'a>>,
    pub strings: FxIndexSet<CowStr<'a>>,
    pub uparams: FxIndexSet<Arc<[LevelPtr<'a>]>>,
    pub bignums: FxIndexSet<BigUint>,
}

impl<'a> LeanDag<'a> {
    /// The export file format does not output the anonymous name and level zero, but the export
    /// program back-references them as though they were the 0th element of their kind; the exporter
    /// implicitly assumes that whatever you're using for storage knows about this convention.
    ///
    /// So when creating a new parser, we need to begin by placing `Anon` and `Zero` in the 0th position
    /// of their backing storage, satisfying the exporter's assumption.
    pub fn new_parser() -> Self {
        let mut out = Self::empty();
        let _ = out.names.insert(Name::Anon);
        let _ = out.levels.insert(Level::Zero);
        out
    }

    pub fn empty() -> Self {
        Self {
            names: new_unique_index_set(),
            levels: new_unique_index_set(),
            exprs: new_unique_index_set(),
            strings: new_fx_index_set(),
            uparams: new_fx_index_set(),
            bignums: new_fx_index_set(),
        }
    }

    /// Used for constructing the name cache;
    pub(crate) fn anonymous(&self) -> NamePtr<'a> {
        debug_assert_eq!(self.names.get_index(0).copied().unwrap(), Name::Anon);
        Ptr::from(DagMarker::ExportFile, 0)
    }

    /// Used for constructing the name cache;
    pub(crate) fn zero(&self) -> LevelPtr<'a> {
        debug_assert_eq!(self.levels.get_index(0).copied().unwrap(), Level::Zero);
        Ptr::from(DagMarker::ExportFile, 0)
    }

    /// Used for constructing the name cache;
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings.get_index_of(s).map(|idx| Ptr::from(DagMarker::ExportFile, idx))
    }

    // Find e.g. `Quot.lift` from "Quot.lift"
    fn find_name(&self, dot_separated_name: &str) -> Option<NamePtr<'a>> {
        let mut pfx = self.anonymous();
        for s in dot_separated_name.split('.') {
            if let Ok(num) = s.parse::<u64>() {
                let hash = hash64!(crate::name::NUM_HASH, pfx, num);
                if let Some(idx) = self.names.get_index_of(&Name::Num(pfx, num, hash)) {
                    pfx = Ptr::from(DagMarker::ExportFile, idx);
                    continue
                }
            } else if let Some(sfx) = self.get_string_ptr(s) {
                let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                if let Some(idx) = self.names.get_index_of(&Name::Str(pfx, sfx, hash)) {
                    pfx = Ptr::from(DagMarker::ExportFile, idx);
                    continue
                }
            }
            return None
        }
        Some(pfx)
    }

    /// If these names are present in the export file, we want to cache
    /// them since we need to retrieve them quite frequently.
    pub(crate) fn mk_name_cache(&self) -> NameCache<'a> {
        NameCache {
            eager_reduce: self.find_name("eagerReduce"),
            quot: self.find_name("Quot"),
            quot_mk: self.find_name("Quot.mk"),
            quot_lift: self.find_name("Quot.lift"),
            quot_ind: self.find_name("Quot.ind"),
            string: self.find_name("String"),
            string_of_list: self.find_name("String.ofList"),
            nat: self.find_name("Nat"),
            nat_zero: self.find_name("Nat.zero"),
            nat_succ: self.find_name("Nat.succ"),
            nat_add: self.find_name("Nat.add"),
            nat_sub: self.find_name("Nat.sub"),
            nat_mul: self.find_name("Nat.mul"),
            nat_pow: self.find_name("Nat.pow"),
            nat_mod: self.find_name("Nat.mod"),
            nat_div: self.find_name("Nat.div"),
            nat_beq: self.find_name("Nat.beq"),
            nat_ble: self.find_name("Nat.ble"),
            nat_gcd: self.find_name("Nat.gcd"),
            nat_xor: self.find_name("Nat.xor"),
            nat_land: self.find_name("Nat.land"),
            nat_lor: self.find_name("Nat.lor"),
            nat_shl: self.find_name("Nat.shiftLeft"),
            nat_shr: self.find_name("Nat.shiftRight"),
            bool_true: self.find_name("Bool.true"),
            bool_false: self.find_name("Bool.false"),
            char: self.find_name("Char"),
            char_of_nat: self.find_name("Char.ofNat"),
            list: self.find_name("List"),
            list_nil: self.find_name("List.nil"),
            list_cons: self.find_name("List.cons"),
        }
    }
}

/// This just caches common names; the values are `Some(x)` if the name
/// is present in the export file, otherwise they're `None`.
#[derive(Debug, Clone, Copy)]
pub struct NameCache<'p> {
    pub(crate) eager_reduce: Option<NamePtr<'p>>,
    pub(crate) quot: Option<NamePtr<'p>>,
    pub(crate) quot_mk: Option<NamePtr<'p>>,
    pub(crate) quot_lift: Option<NamePtr<'p>>,
    pub(crate) quot_ind: Option<NamePtr<'p>>,
    pub(crate) nat: Option<NamePtr<'p>>,
    pub(crate) nat_zero: Option<NamePtr<'p>>,
    pub(crate) nat_succ: Option<NamePtr<'p>>,
    pub(crate) nat_add: Option<NamePtr<'p>>,
    pub(crate) nat_sub: Option<NamePtr<'p>>,
    pub(crate) nat_mul: Option<NamePtr<'p>>,
    pub(crate) nat_pow: Option<NamePtr<'p>>,
    pub(crate) nat_mod: Option<NamePtr<'p>>,
    pub(crate) nat_div: Option<NamePtr<'p>>,
    pub(crate) nat_beq: Option<NamePtr<'p>>,
    pub(crate) nat_ble: Option<NamePtr<'p>>,
    pub(crate) nat_gcd: Option<NamePtr<'p>>,
    pub(crate) nat_xor: Option<NamePtr<'p>>,
    pub(crate) nat_land: Option<NamePtr<'p>>,
    pub(crate) nat_lor: Option<NamePtr<'p>>,
    pub(crate) nat_shr: Option<NamePtr<'p>>,
    pub(crate) nat_shl: Option<NamePtr<'p>>,
    pub(crate) string: Option<NamePtr<'p>>,
    pub(crate) string_of_list: Option<NamePtr<'p>>,
    pub(crate) bool_false: Option<NamePtr<'p>>,
    pub(crate) bool_true: Option<NamePtr<'p>>,
    pub(crate) char: Option<NamePtr<'p>>,
    pub(crate) char_of_nat: Option<NamePtr<'p>>,
    #[allow(dead_code)]
    pub(crate) list: Option<NamePtr<'p>>,
    pub(crate) list_nil: Option<NamePtr<'p>>,
    pub(crate) list_cons: Option<NamePtr<'p>>,
}

pub(crate) struct TcCache<'t> {
    pub(crate) infer_cache_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) infer_cache_no_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) whnf_cache: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) whnf_no_unfolding_cache: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) eq_cache: UnionFind<ExprPtr<'t>>,
    /// A cache of congruence failures during the lazy delta step procedure.
    pub(crate) failure_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    /// Strong reduction is not used during type-checking, this is more of a library/inspection feature.
    pub(crate) strong_cache: UniqueHashMap<(ExprPtr<'t>, bool, bool), ExprPtr<'t>>,
}

impl<'t> TcCache<'t> {
    pub(crate) fn new() -> Self {
        Self {
            infer_cache_check: new_unique_hash_map(),
            infer_cache_no_check: new_unique_hash_map(),
            whnf_cache: new_unique_hash_map(),
            whnf_no_unfolding_cache: new_unique_hash_map(),
            eq_cache: UnionFind::new(),
            failure_cache: new_fx_hash_set(),
            strong_cache: new_unique_hash_map(),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.infer_cache_check.clear();
        self.infer_cache_no_check.clear();
        self.whnf_cache.clear();
        self.whnf_no_unfolding_cache.clear();
        self.eq_cache.clear();
        self.failure_cache.clear();
        self.strong_cache.clear();
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    /// The path to the export file to be checked (if `none`, users must specify `use_stdin: true`)
    pub export_file_path: Option<PathBuf>,

    /// A value indicating whether the type checker should look to stdin to receive the export file.
    #[serde(default)]
    pub use_stdin: bool,

    /// A list of the whitelisted axioms the user wants to allow.
    pub permitted_axioms: Option<Vec<String>>,

    /// A boolean indicating what behavior the typechecker should exhibit when encountering
    /// an axiom in an export file which has not explicitly been named in `permitted_axioms`.
    /// if `unpermitted_axiom_hard_error: true`, the typechecker will fail with a hard error.
    /// if `unpermitted_axiom_hard_error: false`, the typechecker will NOT add the axiom to the environment,
    /// and will continue typechecking in an environment that does not contain the disallowed axiom.
    #[serde(default = "default_true")]
    pub unpermitted_axiom_hard_error: bool,

    /// Number of threads to use for type checking.
    #[serde(default)]
    pub num_threads: usize,

    #[serde(default)] 
    pub nat_extension: bool,
    #[serde(default)] 
    pub string_extension: bool,

    /// A list of declaration names the user wants to be pretty-printed back to them on termination.
    pub pp_declars: Option<Vec<String>>,

    /// Indicates what the typechecker should do when it's been asked to pretty-print a declaration
    /// that is not actually in the environment. We give this option because that scenario is 
    /// strongly indicative of a mismatch between what the user thinks is in the export file and
    /// what is actually in the export file.
    /// If `true`, the typechecker will fail with a hard error. 
    /// If `false`, the typechecker will not fail just because of this.
    #[serde(default = "default_true")]
    pub unknown_pp_declar_hard_error: bool,

    #[serde(default)]
    pub pp_options: PpOptions,

    /// Optionally, a path to write the pretty-printer output to.
    pub pp_output_path: Option<PathBuf>,

    #[serde(default)]
    pub pp_to_stdout: bool,

    #[serde(default)]
    pub print_success_message: bool,

    /// If `true`, the typechecker will print the axioms actually admitted to the environment
    /// when typechecking is finished. 
    #[serde(default = "default_true")]
    pub print_axioms: bool,

    /// If set to `true`, will allow all axioms to be admitted to the environment. 
    /// This is checked so as to be mutually exclusive with any of the axiom allow list/whitelist features.
    #[serde(default)]
    pub unsafe_permit_all_axioms: bool,
}

impl TryFrom<&Path> for Config {
    type Error = Box<dyn Error>;
    fn try_from(p: &Path) -> Result<Config, Self::Error> {
        match OpenOptions::new().read(true).truncate(false).open(p) {
            Err(e) => Err(Box::from(format!("failed to open configuration file: {:?}", e))),
            Ok(config_file) => {
                let config = serde_json::from_reader::<_, Config>(BufReader::new(config_file)).unwrap();
                if config.export_file_path.is_none() && !config.use_stdin {
                    return Err(Box::from(format!("incompatible config options: must specify a path to an export file OR set `use_stdin: true`")))
                }
                if config.export_file_path.is_some() && config.use_stdin {
                    return Err(Box::from(format!("incompatible config options: if an export file path is given, `use_stdin` cannot be `true`")))
                }
                if config.unsafe_permit_all_axioms {
                    if config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!("incompatible config options: unsafe_permit_all_axioms && unpermitted_axioms_hard_error")))
                    }
                    if config.permitted_axioms.is_some() {
                        return Err(Box::from(format!("incompatible config options: unsafe_permit_all_axioms && nonempty permitted_axioms list")))
                    }
                }
                Ok(config)
            }
        }
    }
}

pub enum PpDestination {
    File(BufWriter<std::fs::File>),
    Stdout(BufWriter<std::io::Stdout>),
}

impl PpDestination {
    pub(crate) fn stdout() -> Self { Self::Stdout(BufWriter::new(std::io::stdout())) }
    pub(crate) fn write_line(&mut self, s: String, sep: &str) -> Result<usize, Box<dyn Error>> {
        match self {
            PpDestination::File(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
            PpDestination::Stdout(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
        }
    }
}

impl Config {
    pub fn get_pp_destination(&self) -> Result<Option<PpDestination>, Box<dyn Error>> {
        if let Some(pathbuf) = self.pp_output_path.as_ref() {
            match OpenOptions::new().write(true).truncate(false).open(pathbuf) {
                Ok(file) => Ok(Some(PpDestination::File(BufWriter::new(file)))),
                Err(e) => Err(Box::from(format!("Failed to open pretty printer destination file: {:?}", e))),
            }
        } else if self.pp_to_stdout {
            Ok(Some(PpDestination::stdout()))
        } else {
            Ok(None)
        }
    }

    // Returns the export file, and a list of strings representing the names of "skipped" axioms
    // (axioms which were in the export file, but not allowed by the execution config).
    pub fn to_export_file<'a>(self) -> Result<(ExportFile<'a>, Vec<String>), Box<dyn Error>> {
        if let Some(pathbuf) = self.export_file_path.as_ref() {
            match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
                Ok(file) => crate::parser::parse_export_file(BufReader::new(file), self),
                Err(e) => Err(Box::from(format!("Failed to open export file: {:?}", e))),
            }
        } else if self.use_stdin {
            let reader = BufReader::new(std::io::stdin());
            crate::parser::parse_export_file(reader, self)
        } else {
            panic!("Configuration file must specify en export file path or \"use_stdin\": true")
        }
    }
}

// The intent is to use this for reporting exit status/error info
// when we go back and get rid of all of the `panic!` invocations
// and use more involved error handling.
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct ExitStatus {
    tc_err: Option<String>,
    pp_err: Option<String>
}

