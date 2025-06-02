use crate::env::{DeclarMap, Env, NotationMap};
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
use serde_json::Value as JsonValue;
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
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

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
    /// Whether `Quot` has been checked.
    pub quot_checked: AtomicBool,
    /// Declarations from the export file
    pub declars: DeclarMap<'p>,
    /// Notations from the export file
    pub notations: NotationMap<'p>,
    /// Cached names for convenience (`Quot`, `Nat`, etc.)
    pub name_cache: NameCache<'p>,
    pub config: Config,
}

impl<'p> ExportFile<'p> {
    pub fn new_env(&self) -> Env { Env::new_plus(&self.declars, None, &self.notations) }

    pub fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut TcCtx<'_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        f(&mut ctx)
    }

    pub fn with_tc<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env();
        let mut tc = TypeChecker::new(&mut ctx, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::empty();
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env();
        let mut tc = TypeChecker::new(&mut ctx, &env, Some(d));
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx| ctx.with_pp(f))
    }

    /// Make sure no declaration in the export file contains a reference cycle, either
    /// directly or by unfolding.
    ///
    /// For a declaration `d`, traverses the type and value (if there's a value) ensuring
    /// no `Const(n, _)` reachable by `d` (either directly or by unfolding) can be used to refer back to `d`.
    pub(crate) fn check_no_cycles(&mut self) {
        // This state needs to persist so that we don't unfold the same constants
        let mut state = CycleCheckState::new(self.name_cache);
        for declar_name in self.declars.values().map(|d| d.info().name) {
            state.being_checked.insert(declar_name);
            self.get_declar_unique_names(&mut state, declar_name);
            assert!(!state.unique_names.contains(&declar_name));
            state.checked_declars.insert(declar_name);
            state.clear();
        }
    }

    /// Gather the set of names reachable by `d`, so we can assert that `d` does not
    /// appear therein.
    fn get_declar_unique_names(&self, state: &mut CycleCheckState<'p>, declar_name: NamePtr<'p>) {
        use crate::env::Declar::*;
        let ty = match self.declars.get(&declar_name).map(|d| d.info().ty) {
            None => {
                self.with_ctx(|ctx| eprintln!("declaration {:?} not found", ctx.debug_print(declar_name)));
                panic!()
            }
            Some(ty) => ty,
        };
        self.get_expr_unique_names(state, declar_name, ty);
        match self.declars.get(&declar_name).unwrap() {
            Theorem { val, .. } | Definition { val, .. } | Opaque { val, .. } =>
                self.get_expr_unique_names(state, declar_name, *val),
            Axiom { .. } | Quot { .. } | Inductive(..) | Constructor(..) | Recursor(..) => {}
        };
    }

    /// Gather the names reachable by this expression, unfolding consts IFF they haven't already
    /// been unfolded in a previous check.
    fn get_expr_unique_names(&self, state: &mut CycleCheckState<'p>, declar_name: NamePtr<'p>, e: ExprPtr<'p>) {
        use Expr::*;
        if state.checked_exprs.contains(&e) {
            return
        }
        match self.dag.exprs.get_index(e.idx()).copied().unwrap() {
            Local { .. } => panic!("Export items cannot have free variables"),
            Sort { .. } | Var { .. } => {}
            // FIXME: the components of NatLit/StringLit eventually need to be checked.
            NatLit { .. } => state.found_nat(),
            StringLit { .. } => state.found_string(),
            // If this is a declaration we've already seen and confirmed not to have
            // any cycles, we don't need to unfold it.
            Const { name, .. } if state.checked_declars.contains(&name) => {
                state.unique_names.insert(name);
            }
            // If this is the name of a declaration we haven't already seen
            // and determined to be acyclic, we need to unfold it and check
            // that declaration, because this name might be used to produce a type
            // during inference, or unfolded to produce a value.
            Const { name, .. } => {
                if name == declar_name || state.being_checked.contains(&name) {
                    self.with_ctx(|ctx| eprintln!("Cycle detected in {:?}", ctx.debug_print(name)));
                    panic!()
                }
                state.being_checked.insert(name);
                self.get_declar_unique_names(state, name);
                assert!(state.being_checked.remove(&name));
            }
            Proj { ty_name, structure, .. } => {
                state.unique_names.insert(ty_name);
                self.get_expr_unique_names(state, declar_name, structure);
            }
            App { fun, arg, .. } => {
                self.get_expr_unique_names(state, declar_name, arg);
                self.get_expr_unique_names(state, declar_name, fun);
            }
            Lambda { binder_type, body, .. } | Pi { binder_type, body, .. } => {
                self.get_expr_unique_names(state, declar_name, binder_type);
                self.get_expr_unique_names(state, declar_name, body);
            }
            Let { binder_type, val, body, .. } => {
                self.get_expr_unique_names(state, declar_name, binder_type);
                self.get_expr_unique_names(state, declar_name, val);
                self.get_expr_unique_names(state, declar_name, body);
            }
        };
        state.checked_exprs.insert(e);
    }
}

struct CycleCheckState<'p> {
    nat: bool,
    string: bool,
    name_cache: NameCache<'p>,
    checked_declars: FxHashSet<NamePtr<'p>>,
    checked_exprs: FxHashSet<ExprPtr<'p>>,
    unique_names: FxHashSet<NamePtr<'p>>,
    being_checked: FxHashSet<NamePtr<'p>>,
}

impl<'p> CycleCheckState<'p> {
    fn new(name_cache: NameCache<'p>) -> Self {
        Self {
            nat: false,
            string: false,
            name_cache,
            checked_declars: new_fx_hash_set(),
            checked_exprs: new_fx_hash_set(),
            unique_names: new_fx_hash_set(),
            being_checked: new_fx_hash_set(),
        }
    }

    fn clear(&mut self) {
        self.nat = false;
        self.string = false;
        self.checked_exprs.clear();
        self.unique_names.clear();
        self.being_checked.clear();
    }

    fn found_nat(&mut self) {
        if !self.nat {
            self.unique_names.insert(self.name_cache.nat.unwrap());
            self.unique_names.insert(self.name_cache.nat_zero.unwrap());
            self.unique_names.insert(self.name_cache.nat_succ.unwrap());
            self.nat = true;
        }
    }

    fn found_string(&mut self) {
        if !self.string {
            self.unique_names.insert(self.name_cache.nat.unwrap());
            self.unique_names.insert(self.name_cache.nat_zero.unwrap());
            self.unique_names.insert(self.name_cache.nat_succ.unwrap());
            self.unique_names.insert(self.name_cache.list.unwrap());
            self.unique_names.insert(self.name_cache.list_nil.unwrap());
            self.unique_names.insert(self.name_cache.list_cons.unwrap());
            self.unique_names.insert(self.name_cache.string.unwrap());
            self.unique_names.insert(self.name_cache.string_mk.unwrap());
            self.unique_names.insert(self.name_cache.char.unwrap());
            self.unique_names.insert(self.name_cache.char_of_nat.unwrap());
            self.string = true;
        }
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
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, tdag: &'t mut LeanDag<'t>) -> Self {
        Self { export_file, dag: tdag, dbj_level_counter: 0u16, unique_counter: 0u32, expr_cache: ExprCache::new() }
    }

    pub fn with_tc<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = self.export_file.new_env();
        let mut tc = TypeChecker::new(self, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_env<'x, F, A>(&mut self, env: &'x Env<'x, 't>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let mut tc = TypeChecker::new(self, env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(&mut self, env_ext: &'x DeclarMap<'t>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = crate::env::Env::new_plus(&self.export_file.declars, Some(env_ext), &self.export_file.notations);
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
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body);
        let num_loose_bvars = self
            .num_loose_bvars(binder_type)
            .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
        self.alloc_expr(Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash })
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
            quot: self.find_name("Quot"),
            quot_mk: self.find_name("Quot.mk"),
            quot_lift: self.find_name("Quot.lift"),
            quot_ind: self.find_name("Quot.ind"),
            string: self.find_name("String"),
            string_mk: self.find_name("String.mk"),
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
    pub(crate) string_mk: Option<NamePtr<'p>>,
    pub(crate) bool_false: Option<NamePtr<'p>>,
    pub(crate) bool_true: Option<NamePtr<'p>>,
    pub(crate) char: Option<NamePtr<'p>>,
    pub(crate) char_of_nat: Option<NamePtr<'p>>,
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
        }
    }

    pub(crate) fn clear(&mut self) {
        self.infer_cache_check.clear();
        self.infer_cache_no_check.clear();
        self.whnf_cache.clear();
        self.whnf_no_unfolding_cache.clear();
        self.eq_cache.clear();
        self.failure_cache.clear();
    }
}

pub(crate) fn get_field<'a>(k: &str, j: &'a JsonValue) -> Option<&'a JsonValue> { j.get(k).filter(|v| !v.is_null()) }

pub(crate) fn get_bool(k: &str, j: &JsonValue, default: bool) -> Result<bool, Box<dyn Error>> {
    match get_field(k, j) {
        None => Ok(default),
        Some(b) =>
            b.as_bool().ok_or_else(|| Box::<dyn Error>::from(format!("json field {} must be a bool; found {:?}", k, b))),
    }
}

pub(crate) fn get_nat(k: &str, j: &JsonValue, default: usize) -> Result<usize, Box<dyn Error>> {
    match get_field(k, j) {
        None => Ok(default),
        Some(b) => b
            .as_u64()
            .map(|n| n as usize)
            .ok_or_else(|| Box::<dyn Error>::from(format!("json field {} must be a nat; found {:?}", k, b))),
    }
}

pub(crate) fn get_path_buf(k: &str, j: &JsonValue) -> Result<Option<PathBuf>, Box<dyn Error>> {
    match get_field(k, j) {
        None => Ok(None),
        Some(b) => b
            .as_str()
            .map(|s| Some(PathBuf::from(s)))
            .ok_or_else(|| Box::<dyn Error>::from(format!("json field {} must be a path; found {:?}", k, b))),
    }
}

pub(crate) fn get_string(k: &str, j: &JsonValue, default: String) -> Result<String, Box<dyn Error>> {
    match get_field(k, j) {
        None => Ok(default),
        Some(b) => b
            .as_str()
            .map(|s| s.to_owned())
            .ok_or_else(|| Box::<dyn Error>::from(format!("json field {} must be a string; found {:?}", k, b))),
    }
}

pub(crate) fn get_list(k: &str, j: &JsonValue) -> Result<Vec<String>, Box<dyn Error>> {
    match get_field(k, j) {
        None => Ok(Vec::new()),
        Some(b) => match b.as_array() {
            None => Err(Box::<dyn Error>::from(format!("json field {} must be a list of strings; found {:?}", k, b))),
            Some(vs) => {
                let mut out = Vec::new();
                for j in vs {
                    out.push(j.as_str().map(|s| s.to_owned()).ok_or_else(|| {
                        Box::<dyn Error>::from(format!("elemsnts of {} must be strings, found {:?}", k, j))
                    })?);
                }
                Ok(out)
            }
        },
    }
}

pub struct Config {
    pub export_file_path: Option<PathBuf>,
    pub use_stdin: bool,
    pub permitted_axioms: Vec<String>,
    pub unpermitted_axiom_hard_error: bool,
    pub num_threads: usize,
    pub nat_extension: bool,
    pub string_extension: bool,
    pub pp_declars: Vec<String>,
    pub pp_options: PpOptions,
    pub pp_output_path: Option<PathBuf>,
    pub pp_to_stdout: bool,
    pub print_success_message: bool,
}

impl TryFrom<&Path> for Config {
    type Error = Box<dyn Error>;
    fn try_from(p: &Path) -> Result<Config, Self::Error> {
        match OpenOptions::new().read(true).truncate(false).open(p) {
            Err(e) => Err(Box::from(format!("failed to open configuration file: {:?}", e))),
            Ok(config_file) => {
                let json: JsonValue = serde_json::from_reader(BufReader::new(config_file))?;
                Config::try_from(&json)
            }
        }
    }
}

const CONFIG_OPTIONS: [&str; 20] = [
    "export_file_path",
    "use_stdin",
    "permitted_axioms",
    "num_threads",
    "pp_declars",
    "nat_extension",
    "string_extension",
    "pp_output_path",
    "pp_to_stdout",
    "print_success_message",
    "pp_options",
    "all",
    "explicit",
    "universes",
    "notation",
    "indent",
    "width",
    "declar_sep",
    "unpermitted_axiom_hard_error",
    "proofs"
];

fn keys_recognized(j: &JsonValue) -> Result<(), Box<dyn Error>> {
    fn keys_recognized_aux(j: &JsonValue, unrecognized_keys: &mut Vec<String>) {
        if let Some(map) = j.as_object() {
            for (k, v) in map.iter() {
                if !CONFIG_OPTIONS.contains(&k.as_str()) {
                    unrecognized_keys.push(k.to_owned());
                }
                keys_recognized_aux(v, unrecognized_keys);
            }
        }
    }
    let mut unrecognized_keys = Vec::new();
    keys_recognized_aux(j, &mut unrecognized_keys);
    if !unrecognized_keys.is_empty() {
        Err(Box::from(format!("unrecognized configuration options: {:?}", unrecognized_keys)))
    } else {
        Ok(())
    }
}

impl TryFrom<&JsonValue> for Config {
    type Error = Box<dyn std::error::Error>;

    fn try_from(v: &JsonValue) -> Result<Self, Self::Error> {
        keys_recognized(v)?;
        Ok(Self {
            export_file_path: get_path_buf("export_file_path", v)?,
            use_stdin: get_bool("use_stdin", v, false)?,
            permitted_axioms: get_list("permitted_axioms", v)?,
            unpermitted_axiom_hard_error: get_bool("unpermitted_axiom_hard_error", v, true)?,
            num_threads: get_nat("num_threads", v, 1)?,
            pp_declars: get_list("pp_declars", v)?,
            nat_extension: get_bool("nat_extension", v, false)?,
            string_extension: get_bool("string_extension", v, false)?,
            pp_output_path: get_path_buf("pp_output_path", v)?,
            pp_to_stdout: get_bool("pp_to_stdout", v, false)?,
            print_success_message: get_bool("print_success_message", v, true)?,
            pp_options: match v.get("pp_options") {
                Some(options) if !options.is_null() => PpOptions::try_from(options)?,
                _ => PpOptions::default(),
            },
        })
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

    pub fn to_export_file<'a>(self) -> Result<ExportFile<'a>, Box<dyn Error>> {
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
