use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::{ Hash, BuildHasherDefault };
use std::marker::PhantomData;

use rustc_hash::FxHasher;
use indexmap::{ IndexMap, IndexSet };

use crate::name::{ NamePtr, Name, Name::* };
use crate::level::{ LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, LocalSerial };
use crate::env::{ Declar, DeclarView, RecRule, Notation, DeclarPtr, DeclarsPtr };
use crate::tc::eq::EqResult;
use crate::tc::infer::InferFlag;
use crate::{ arena_item, has_list, trace_env };
use crate::trace::items::HasTraceItem;
use crate::trace::{ IsTracer, TraceMgr };
use crate::trace::steps::*;


pub struct TryToken;

pub type FxIndexSet<A> = IndexSet<A, BuildHasherDefault<FxHasher>>;
pub type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

use List::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct EnvZst;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct LiveZst;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct TcZst;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct PfinderZst;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ptr2<PH> {
    E(usize, PH, EnvZst),
    L(usize, PH, LiveZst),
    P(usize, PH, PfinderZst),
}

pub type Ptr<'a, A> = Ptr2<PhantomData<&'a A>>;

impl<'a, A> Ptr<'a, A> {
    pub fn in_env(self) -> bool {
        match self {
            Ptr::E(..) => true,
            _ => false
        }
    }

    pub fn ptr_idx(self) -> usize {
        match self {
            | Ptr::E(n, ..)
            | Ptr::L(n, ..)
            | Ptr::P(n, ..) => n
        }
    }
}

pub trait HasMkPtr : Copy + Default + Debug {
    fn mk_ptr<'a, A>(self, index : usize) -> Ptr<'a, A>;
}

impl HasMkPtr for EnvZst {
    fn mk_ptr<'a, A>(self, index : usize) -> Ptr<'a, A> {
        Ptr::E(index, PhantomData, self)
    }
}

impl HasMkPtr for LiveZst {
    fn mk_ptr<'a, A>(self, index : usize) -> Ptr<'a, A> {
        Ptr::L(index, PhantomData, self)
    }
}

impl HasMkPtr for PfinderZst {
    fn mk_ptr<'a, A>(self, index : usize) -> Ptr<'a, A> {
        Ptr::P(index, PhantomData, self)
    }
}


pub type ListPtr<'a, A> = Ptr<'a, List<'a, A>>;


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum List<'a, A> {
    Nil,
    Cons(Ptr<'a, A>, ListPtr<'a, A>)
}


pub struct Set<A, Z : HasMkPtr> {
    marker : Z,
    elems    : FxIndexSet<A>,
}

impl<'a, A, Z> Set<A, Z> 
where A : Eq + Hash,
      Z : HasMkPtr {
    pub fn new() -> Self {
        Set {
            marker      : Default::default(),
            elems       : FxIndexSet::with_hasher(Default::default()),
        }
    }

    pub fn get_elem(&self, index : usize, _ : PhantomData<&'_ A>, _ : Z) -> &A {
        self.elems.get_index(index).expect("Checked `None`")
    }


    pub fn extend_safe(&self, index : usize, _z : Z) -> Ptr<'a, A> {
        self.marker.mk_ptr(index)
    }

    fn retrieve(&self, index : usize) -> Ptr<'a, A> {
        self.marker.mk_ptr(index)
    }

    pub fn insert_elem(&mut self, elem : A) -> Ptr<'a, A> {
        let (idx, _) = self.elems.insert_full(elem);
        self.marker.mk_ptr(idx)
    }

    fn check_dupe(&self, elem : &A) -> Option<Ptr<'a, A>> {
        self
        .elems
        .get_full(elem)
        .map(|(index, _)| self.marker.mk_ptr(index))
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }
}


pub struct Store<'a, Z : HasMkPtr> {
    pub strings : Set<String, Z>,

    pub names : Set<Name<'a>, Z>,
    pub name_lists : Set<List<'a, Name<'a>>, Z>,

    pub levels : Set<Level<'a>, Z>,
    pub level_lists : Set<List<'a, Level<'a>>, Z>,

    pub exprs : Set<Expr<'a>, Z>,
    pub expr_lists : Set<List<'a, Expr<'a>>, Z>,

    pub rec_rules : Set<RecRule<'a>, Z>,
    pub rec_rule_lists : Set<List<'a, RecRule<'a>>, Z>,
    pub declars : Set<Declar<'a>, Z>,
    pub declar_lists : Set<List<'a, Declar<'a>>, Z>
}

impl<'a, Z : HasMkPtr> Store<'a, Z> {
    pub fn new() -> Self {
        Store {
            strings : Set::new(),
            names : Set::new(),
            name_lists : Set::new(),
            levels : Set::new(),
            level_lists : Set::new(),
            exprs : Set::new(),
            expr_lists : Set::new(),
            rec_rules : Set::new(),
            rec_rule_lists : Set::new(),
            declars : Set::new(),
            declar_lists : Set::new(),
        }
    }

}

pub struct ExprCache<'a, Z> {
    marker : PhantomData<Z>,
    pub abstr_cache       : FxHashMap<(ExprPtr<'a>, u16), (ExprPtr<'a>, Step<AbstrAuxZst>)>,
    pub find_cache        : FxHashMap<ExprPtr<'a>, (bool, Step<HasIndOccZst>)>,
    pub inst_cache        : FxHashMap<(ExprPtr<'a>, ExprsPtr<'a>, u16), (ExprPtr<'a>, Step<InstAuxZst>)>,
    pub subst_cache       : FxHashMap<(ExprPtr<'a>, LevelsPtr<'a>, LevelsPtr<'a>), (ExprPtr<'a>, Step<SubstEZst>)>,
    pub height_cache      : FxHashMap<ExprPtr<'a>, (u16, Step<CalcHeightAuxZst>)>,
    pub fold_cache        : FxHashMap<(ExprPtr<'a>, ExprsPtr<'a>), (ExprPtr<'a>, Step<FoldlAppsZst>)>,
    pub unfold_cache      : FxHashMap<ExprPtr<'a>, ((ExprPtr<'a>, ExprsPtr<'a>), Step<UnfoldAppsAuxZst>)>,
}

pub fn new_map<K : Hash + Eq, V>() -> FxHashMap<K, V> {
    FxHashMap::with_hasher(Default::default())
}

impl<'a, Z> ExprCache<'a, Z> {
    pub fn new() -> Self {
        ExprCache {
            marker : PhantomData,
            abstr_cache      : FxHashMap::with_hasher(Default::default()),
            find_cache       : FxHashMap::with_hasher(Default::default()),            
            subst_cache      : FxHashMap::with_hasher(Default::default()),
            inst_cache       : FxHashMap::with_hasher(Default::default()),
            height_cache     : FxHashMap::with_hasher(Default::default()),
            fold_cache       : FxHashMap::with_hasher(Default::default()),
            unfold_cache     : FxHashMap::with_hasher(Default::default()),
        }
    }
}

pub struct TcCache<'a, Z> {
    marker : PhantomData<Z>,
    infer_cache   : FxHashMap<(ExprPtr<'a>, InferFlag), (ExprPtr<'a>, Step<InferZst>)>,
    eq_cache      : FxHashMap<(ExprPtr<'a>, ExprPtr<'a>), (EqResult, Step<DefEqZst>)>,
    whnf_cache    : FxHashMap<ExprPtr<'a>, (ExprPtr<'a>, Step<WhnfZst>)>,
    args_eq_cache : FxHashMap<(ExprsPtr<'a>, ExprsPtr<'a>), (EqResult, Step<ArgsEqAuxZst>)>,
}

impl<'a, Z> TcCache<'a, Z> {
    fn new() -> Self {
        TcCache {
            marker : PhantomData,
            infer_cache   : FxHashMap::with_hasher(Default::default()),
            eq_cache      : FxHashMap::with_hasher(Default::default()),
            whnf_cache    : FxHashMap::with_hasher(Default::default()),
            args_eq_cache : FxHashMap::with_hasher(Default::default()),
        }
    }
}

pub struct Env<'e, T : IsTracer> {
    pub store : Store<'e, EnvZst>,
    pub declars : FxIndexMap<NamePtr<'e>, (DeclarPtr<'e>, Step<AdmitDeclarZst>)>,
    pub notations : FxHashMap<NamePtr<'e>, Notation<'e>>,
    pub is_actual : bool,
    pub next_local : u64,
    pub next_ind_serial : u16,
    pub quot_mk : Option<NamePtr<'e>>,
    pub quot_lift : Option<NamePtr<'e>>,
    pub quot_ind : Option<NamePtr<'e>>,
    pub trace_mgr : TraceMgr<T>,
}

impl<'l, 'e : 'l, T : 'e + IsTracer> Env<'e, T> {
    pub fn new(tracer : T) -> Self {
        let mut env = Env {
            store : Store::new(),
            declars : FxIndexMap::with_hasher(Default::default()),
            notations : FxHashMap::with_hasher(Default::default()),
            is_actual : false,
            next_local : 0u64,
            next_ind_serial : 0u16,
            quot_mk : None,
            quot_lift : None,
            quot_ind : None,
            trace_mgr : TraceMgr::new(tracer),
        };

        Anon.alloc(&mut env);
        Zero.alloc(&mut env);
        Nil::<Name>.alloc(&mut env);
        Nil::<Level>.alloc(&mut env);
        Nil::<Expr>.alloc(&mut env);
        Nil::<RecRule>.alloc(&mut env);
        Nil::<Declar>.alloc(&mut env);
        env
    }
    
    pub fn as_live(&'l mut self) -> Live<'l, 'e, T> {
        Live {
            env : self,
            store : Store::new(),
            expr_cache : ExprCache::new(),
            pfinder_store : Store::new(),
        }
    }

    pub fn next_ind_serial(&mut self) -> u16 {
        let curr = self.next_ind_serial;
        self.next_ind_serial += 1;
        curr
    }

    pub fn num_declars(&self) -> usize {
        self.declars.len()
    }

    pub fn trace_env(&mut self) {
        {
            let len = self.store.strings.elems.len();
            for i in 0..len {
                let ptr = self.store.strings.retrieve(i);
                ptr.trace_item(self);
            }

        }

        trace_env!(self, names, name_lists, true);
        trace_env!(self, levels, level_lists, true);
        trace_env!(self, exprs, expr_lists, false);
        trace_env!(self, rec_rules, rec_rule_lists, false);
        trace_env!(self, declars, declar_lists, false);
    }
}

pub struct Live<'l, 'e : 'l, T : IsTracer> {
    pub env : &'l mut Env<'e, T>,
    pub store : Store<'l, LiveZst>,
    pfinder_store : Store<'l, PfinderZst>,
    expr_cache : ExprCache<'l, LiveZst>,
}

impl<'t, 'l : 't, 'e : 'l, T> Live<'l, 'e, T> 
where T : 'e + IsTracer {
    pub fn as_tc(&'t mut self, dec_uparams : Option<LevelsPtr<'l>>, safe_only : Option<bool>) -> Tc<'t, 'l, 'e, T> {
        let dec_uparams = dec_uparams.unwrap_or_else(|| Nil::<Level>.alloc(self));
        Tc {
            live : self,
            dec_uparams,
            safe_only : safe_only.unwrap_or(false),
            tc_cache : TcCache::new(),
            pfinder_tc_cache : TcCache::new(),
            pfinder_expr_cache : ExprCache::new(),
        }
    }

    pub fn last_admit(&mut self) -> Option<Step<AdmitDeclarZst>> {
        match self.env.declars.values().last() {
            None => None,
            Some((_, admitted_at)) => Some(*admitted_at)
        }
    }

    // In the specification, we allow declaration steps to append a list 
    // of declarations as long as the list meets certain requirements.
    pub fn admit_declars(
        &mut self, 
        ds : DeclarsPtr<'l>,
        h1 : Step<AdmitDeclarZst>
    ) {
        let mut ds = if self.env.is_actual {
            assert!(ds.in_env());
            ds.extend_lifetime(self.env)
        } else {
            ds.insert_env(self.env, &self.store)
        };

        while let Cons(hd, tl) = ds.read(self.env) {
            assert!(hd.in_env());
            let name = hd.name(self.env);
            self.env.declars.insert(name, (hd, h1));
            ds = tl;
        }
    }

    pub fn admit_declar(
        &mut self, 
        d : DeclarPtr<'l>,
        h1 : Step<AdmitDeclarZst>
    ) {
        assert!(self.env.declars.get(&d.name(self)).is_none());
        if self.env.is_actual {
            assert!(d.in_env());
            let d = d.extend_lifetime(self.env);
            let name = d.name(self.env);
            self.env.declars.insert(name, (d, h1));
        } else {
            let d = d.insert_env(self.env, &self.store);
            let name = d.name(self.env);
            self.env.declars.insert(name, (d, h1));
        }
    }
}

pub struct Tc<'t, 'l : 't, 'e : 'l, T : IsTracer> {
    pub live : &'t mut Live<'l, 'e, T>,
    dec_uparams : LevelsPtr<'l>,
    safe_only : bool,
    tc_cache : TcCache<'l, TcZst>,
    pfinder_tc_cache : TcCache<'l, PfinderZst>,
    pfinder_expr_cache : ExprCache<'l, PfinderZst>,
}

pub struct Pfinder<'p, 't : 'p, 'l : 't, 'e : 'l, T : IsTracer> {
    tc : &'p mut Tc<'t, 'l, 'e, T>,
    dec_uparams : LevelsPtr<'l>,
    safe_only : bool,
}

pub trait IsTc<'t, 'l : 't, 'e : 'l> : IsLiveCtx<'l> {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 't, 'l, 'e, Self::Tracer>;
    fn safe_only(&self) -> bool;
    fn dec_uparams(&self) -> LevelsPtr<'l>;
    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)>;

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<InferZst>)>;
    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<(EqResult, Step<DefEqZst>)>;
    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<WhnfZst>)>;
    fn check_args_eq_cache(&self, l : ExprsPtr<'l>, r : ExprsPtr<'l>) -> Option<(EqResult, Step<ArgsEqAuxZst>)>;

    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : (ExprPtr<'l>, Step<InferZst>));
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, v : (EqResult, Step<DefEqZst>));
    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : (ExprPtr<'l>, Step<WhnfZst>));
    fn insert_args_eq_cache(&mut self, l : ExprsPtr<'l>, r : ExprsPtr<'l>, v : (EqResult, Step<ArgsEqAuxZst>));
}

impl<'t, 'l : 't, 'e : 'l, T> IsTc<'t, 'l, 'e> for Tc<'t, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 't, 'l, 'e, Self::Tracer> {
        let dec_uparams = self.dec_uparams;
        let safe_only  = self.safe_only;
        Pfinder {
            tc : self,
            dec_uparams,
            safe_only,
        }
    }
    
    fn safe_only(&self) -> bool {
        self.safe_only
    }

    fn dec_uparams(&self) -> LevelsPtr<'l> {
        self.dec_uparams
    }

    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)> {
        Some((
             self.live.env.quot_mk?,
             self.live.env.quot_lift?,
             self.live.env.quot_ind?
            ))
    }

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<InferZst>)> {
        self.tc_cache.infer_cache.get(&(k, flag)).copied()
    }

    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<(EqResult, Step<DefEqZst>)> {
        self.tc_cache.eq_cache.get(&(l, r)).copied()
    }

    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<WhnfZst>)> {
        self.tc_cache.whnf_cache.get(k).copied()
    }

    fn check_args_eq_cache(&self, l : ExprsPtr<'l>, r : ExprsPtr<'l>) -> Option<(EqResult, Step<ArgsEqAuxZst>)> {
        self.tc_cache.args_eq_cache.get(&(l, r)).copied()
    }


    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : (ExprPtr<'l>, Step<InferZst>)) {
        self.tc_cache.infer_cache.insert((k, flag), v);
    }
    
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, v : (EqResult, Step<DefEqZst>)) {
        self.tc_cache.eq_cache.insert((l, r), v);
    }

    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : (ExprPtr<'l>, Step<WhnfZst>)) {
        self.tc_cache.whnf_cache.insert(k, v);
    }
    
    fn insert_args_eq_cache(&mut self, l : ExprsPtr<'l>, r : ExprsPtr<'l>, v : (EqResult, Step<ArgsEqAuxZst>)) {
        self.tc_cache.args_eq_cache.insert((l, r), v);
    }


}

impl<'p, 't : 'p, 'l : 't, 'e : 'l, T> IsTc<'t, 'l, 'e> for Pfinder<'p, 't, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 't, 'l, 'e, T> {
        Pfinder {
            tc : self.tc,
            dec_uparams : self.dec_uparams,
            safe_only : self.safe_only,
        }
    }
    
    fn safe_only(&self) -> bool {
        self.safe_only
    }

    fn dec_uparams(&self) -> LevelsPtr<'l> {
        self.dec_uparams
    }

    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)> {
        Some((
            self.tc.live.env.quot_mk?,
            self.tc.live.env.quot_lift?,
            self.tc.live.env.quot_ind?
        ))
    }    

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<InferZst>)> {
        self.tc.tc_cache.infer_cache.get(&(k, flag))
        .or_else(|| self.tc.pfinder_tc_cache.infer_cache.get(&(k, flag)))
        .copied()
    }

    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<(EqResult, Step<DefEqZst>)> {
        self.tc.tc_cache.eq_cache.get(&(l, r))
        .or_else(|| self.tc.pfinder_tc_cache.eq_cache.get(&(l, r)))
        .copied()
    }

    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<WhnfZst>)> {
        self.tc.tc_cache.whnf_cache.get(k)
        .or_else(|| self.tc.pfinder_tc_cache.whnf_cache.get(k))
        .copied()
    }
    
    
    fn check_args_eq_cache(&self, l : ExprsPtr<'l>, r : ExprsPtr<'l>) -> Option<(EqResult, Step<ArgsEqAuxZst>)> {
        self.tc.tc_cache.args_eq_cache.get(&(l, r))
        .or_else(|| self.tc.pfinder_tc_cache.args_eq_cache.get(&(l, r)))
        .copied()
    }

    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : (ExprPtr<'l>, Step<InferZst>)) {
        self.tc.pfinder_tc_cache.infer_cache.insert((k, flag), v);

    }
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, step : (EqResult, Step<DefEqZst>)) {
        self.tc.pfinder_tc_cache.eq_cache.insert((l, r), step);
    }

    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : (ExprPtr<'l>, Step<WhnfZst>)) {
        self.tc.pfinder_tc_cache.whnf_cache.insert(k, v);
    }

    fn insert_args_eq_cache(&mut self, l : ExprsPtr<'l>, r : ExprsPtr<'l>, v : (EqResult, Step<ArgsEqAuxZst>)) {
        self.tc.pfinder_tc_cache.args_eq_cache.insert((l, r), v);
    }
    
}


pub trait IsCtx<'a> {
    type Writable : HasMkPtr;
    type Tracer : 'a + IsTracer;
    const IS_PFINDER : bool;

    fn env_store(&self) -> &Store<'a, EnvZst>;
    fn live_store(&self) -> Option<&Store<'a, LiveZst>>;
    fn pfinder_store(&self) -> Option<&Store<'a, PfinderZst>>;
    fn mut_store(&mut self) -> &mut Store<'a, Self::Writable>;
    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'a>, Step<AdmitDeclarZst>)>;
    fn get_declar_view(&self, n : NamePtr) -> Option<(DeclarView<'a>, Step<AdmitDeclarZst>)>;
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer>;
    fn tracer(&mut self) -> &mut Self::Tracer {
        &mut self.mut_mgr().tracer
    }
}

impl<'e, T> IsCtx<'e> for Env<'e, T> 
where T : 'e + IsTracer {
    type Writable = EnvZst;
    type Tracer = T;
    const IS_PFINDER : bool = false;

    fn env_store(&self) -> &Store<'e, EnvZst> {
        &self.store
    }

    fn live_store(&self) -> Option<&Store<'e, LiveZst>> {
        None
    }

    fn pfinder_store(&self) -> Option<&Store<'e, PfinderZst>> {
        None
    }

    fn mut_store(&mut self) -> &mut Store<'e, Self::Writable> {
        &mut self.store
    }

    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'e>, Step<AdmitDeclarZst>)> {
        self.declars.get(&n).copied()
    }

    fn get_declar_view(&self, n : NamePtr) -> Option<(DeclarView<'e>, Step<AdmitDeclarZst>)> {
        self.get_declar(n)
        .map(|(d, h)| (d.as_view(self), h))
    }
    
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        &mut self.trace_mgr
    }
}

impl<'l, 'e : 'l, T> IsCtx<'l> for Live<'l, 'e, T>
where T : 'l + IsTracer {
    type Writable = LiveZst;
    type Tracer = T;
    const IS_PFINDER : bool = false;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        &self.env.store
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        Some(&self.store)
    }

    fn pfinder_store(&self) -> Option<&Store<'l, PfinderZst>> {
        None
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        &mut self.store
    }

    
    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclarZst>)> {
        self.env.declars.get(&n).copied()
    }

    fn get_declar_view(&self, n : NamePtr) -> Option<(DeclarView<'l>, Step<AdmitDeclarZst>)> {
        self.get_declar(n)
        .map(|(d, h)| (d.as_view(self), h))
    }
    
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        &mut self.env.trace_mgr
    }

    
}

impl<'t, 'l : 't, 'e : 'l, T> IsCtx<'l> for Tc<'t, 'l, 'e, T>
where T : 'l + IsTracer {
    type Writable = LiveZst;
    type Tracer = T;
    const IS_PFINDER : bool = false;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        &self.live.env.store
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        Some(&self.live.store)
    }

    fn pfinder_store(&self) -> Option<&Store<'l, PfinderZst>> {
        None
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        &mut self.live.store
    }

    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclarZst>)> {
        self.live.env.declars.get(&n).copied()
    }
    
    fn get_declar_view(&self, n : NamePtr) -> Option<(DeclarView<'l>, Step<AdmitDeclarZst>)> {
        self.get_declar(n)
        .map(|(d, h)| (d.as_view(self), h))
    }

    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        self.live.mut_mgr()
    }
}

impl<'p, 't : 'p, 'l : 't, 'e : 'l, T> IsCtx<'l> for Pfinder<'p, 't, 'l, 'e, T>
where T : 'l + IsTracer {
    type Writable = PfinderZst;
    type Tracer = T;
    const IS_PFINDER : bool = true;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        &self.tc.live.env.store
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        Some(&self.tc.live.store)
    }

    fn pfinder_store(&self) -> Option<&Store<'l, PfinderZst>> {
        Some(&self.tc.live.pfinder_store)
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        &mut self.tc.live.pfinder_store
    }


    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclarZst>)> {
        self.tc.live.env.declars.get(&n).copied()
    }

    fn get_declar_view(&self, n : NamePtr) -> Option<(DeclarView<'l>, Step<AdmitDeclarZst>)> {
        self.get_declar(n)
        .map(|(d, h)| (d.as_view(self), h))
    }

    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        self.tc.live.mut_mgr()
    }
}


// Gives access to expression caches.
pub trait IsLiveCtx<'l> : IsCtx<'l> {
    fn expr_cache(&mut self) -> &mut ExprCache<'l, Self::Writable>;
    fn next_local(&mut self) -> LocalSerial;
}


impl<'l, 'e : 'l, T> IsLiveCtx<'l> for Live<'l, 'e, T> 
where T : 'l + IsTracer {
    fn expr_cache(&mut self) -> &mut ExprCache<'l, LiveZst> {
        &mut self.expr_cache
    }
    
    fn next_local(&mut self) -> LocalSerial {
        let this_serial = self.env.next_local;
        self.env.next_local += 1;
        LocalSerial(this_serial)
    }
}

impl<'t, 'l : 't, 'e : 'l, T> IsLiveCtx<'l> for Tc<'t, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn expr_cache(&mut self) -> &mut ExprCache<'l, LiveZst> {
        &mut self.live.expr_cache
    }
    
    fn next_local(&mut self) -> LocalSerial {
        self.live.next_local()
    }
}

impl<'p, 't : 'p, 'l : 't, 'e : 'l, T> IsLiveCtx<'l> for Pfinder<'p, 't, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn expr_cache(&mut self) -> &mut ExprCache<'l, PfinderZst> {
        &mut self.tc.pfinder_expr_cache
    }
    
    fn next_local(&mut self) -> LocalSerial {
        self.tc.live.next_local()
    }
}

// Strings are a pain since they're the only type we deal with
// that isn't copy.
pub fn alloc_str<'a>(s : String, ctx : &mut impl IsCtx<'a>) -> Ptr<'a, String> {
    ctx
    .env_store()
    .strings
    .check_dupe(&s)
    .or_else(|| ctx.live_store().and_then(|st| st.strings.check_dupe(&s)))
    .unwrap_or_else(|| {
        let result = ctx.mut_store().strings.insert_elem(s);
        result.trace_item(ctx);
        result
    })
}

impl<'s, 'a : 's> Ptr<'a, String> {
    pub fn read(self, ctx : &'s impl IsCtx<'a>) -> &'s String {
        match self {
            Ptr::E(index, h, z) => &ctx.env_store().strings.get_elem(index, h, z),
            Ptr::L(index, h, z) => &ctx.live_store().expect("Strings failed to read live store!").strings.get_elem(index, h, z),
            Ptr::P(..) => unreachable!("Pfinder store can't hold strings!")
        }
    }
}

arena_item!{ 'a, 'e, 'l, Name, names }
arena_item!{ 'a, 'e, 'l, Level, levels }
arena_item!{ 'a, 'e, 'l, Expr, exprs }
arena_item!{ 'a, 'e, 'l, RecRule, rec_rules }
arena_item!{ 'a, 'e, 'l, Declar, declars }
has_list!{ 'a, 'e, 'l, Name, name_lists }
has_list!{ 'a, 'e, 'l, Level, level_lists }
has_list!{ 'a, 'e, 'l, Expr, expr_lists }
has_list!{ 'a, 'e, 'l, Declar, declar_lists }
has_list!{ 'a, 'e, 'l, RecRule, rec_rule_lists }

#[macro_export]
macro_rules! arena_item {
    ( $short:lifetime, $env:lifetime, $live:lifetime, $base:ident, $field:ident ) => {
        impl<$short> $base<$short> {
            pub fn check_dupe(self, ctx : &impl IsCtx<$short>) -> Option<Ptr<$short, $base<$short>>> {
                ctx.env_store().$field.check_dupe(&self)
                .or_else(|| ctx.live_store().and_then(|sto| sto.$field.check_dupe(&self)))
                .or_else(|| ctx.pfinder_store().and_then(|sto| sto.$field.check_dupe(&self)))
            }

            pub fn alloc(self, ctx : &mut impl IsCtx<$short>) -> Ptr<$short, $base<$short>> {
                if let Some(dupe_ptr) = self.check_dupe(ctx) {
                    dupe_ptr
                } else {
                    let r = ctx.mut_store().$field.insert_elem(self);
                    r.trace_item(ctx);
                    r
                }
            }
        }

        impl<$short> Ptr<$short, $base<$short>> {
            pub fn read(self, ctx : &impl IsCtx<$short>) -> $base<$short> {
                match self {
                    Ptr::E(index, h, z) => *ctx.env_store().$field.get_elem(index, h, z),
                    Ptr::L(index, h, z) => *ctx.live_store()
                                               .expect("Failed to get live store")
                                               .$field
                                               .get_elem(index, h, z),
                    Ptr::P(index, h, z) => *ctx.pfinder_store()
                                               .expect("Failed to get pfinder store! Ptr")
                                               .$field
                                               .get_elem(index, h, z)
                }
            }

            pub fn insert_env<$live, $env>(self, env : &mut Env<$env, impl $env + IsTracer>, live : &Store<$live, LiveZst>) -> Ptr<$env, $base<$env>> {
                match self {
                    Ptr::E(index, _, z) => {
                        let underlying_data = self.read(env);
                        let p = env.store.$field.extend_safe(index, z);
                        assert_eq!(underlying_data, p.read(env));
                        p
                    },
                    Ptr::L(index, h, z) => {
                        live.$field.get_elem(index, h, z).insert_env(env, live)
                    },
                    Ptr::P(..) => unreachable!("P items hould never be put in the environment!")
                }
            }

            pub fn extend_lifetime<$env>(self, env : &mut Env<$env, impl $env + IsTracer>) -> Ptr<$env, $base<$env>> {
                match self {
                    Ptr::E(index, _, z) => {
                        let underlying_data = self.read(env);
                        let p = env.store.$field.extend_safe(index, z);
                        assert_eq!(underlying_data, p.read(env));
                        p
                    },
                    _ => unreachable!("Can only `extend_lifetime()` for environment items!")
                }
            }
        }
        
        impl<$short> HasNanodaDbg<$short> for Ptr<$short, $base<$short>> {
            fn nanoda_dbg(self, ctx : &impl IsCtx<$short>) -> String {
                self.read(ctx).nanoda_dbg(ctx)
            }
        }                

    };
}

#[macro_export]
macro_rules! has_list {
    ( $short:lifetime, $env:lifetime, $live:lifetime, $base:ident, $list_field:ident ) => {
        impl<$short> List<$short, $base<$short>> {
            pub fn alloc(self, ctx : &mut impl IsCtx<$short>) -> ListPtr<$short, $base<$short>> {
                if let Some(dupe_ptr) = self.check_dupe(ctx) {
                    dupe_ptr
                } else {
                    let r = ctx.mut_store().$list_field.insert_elem(self);
                    r.trace_item(ctx);
                    r
                }
            }            

            pub fn check_dupe(self, ctx : &impl IsCtx<$short>) -> Option<ListPtr<$short, $base<$short>>> {
                ctx.env_store().$list_field.check_dupe(&self)
                .or_else(|| ctx.live_store().and_then(|sto| sto.$list_field.check_dupe(&self)))
                .or_else(|| ctx.pfinder_store().and_then(|sto| sto.$list_field.check_dupe(&self)))
            }


           pub fn insert_env<$live, $env>(self, env : &mut Env<$env, impl $env + IsTracer>, live : &Store<$live, LiveZst>) -> ListPtr<$env, $base<$env>> {
               match self {
                   Nil => unreachable!("Nil should always be in the environment!"),
                   Cons(hd, tl) => {
                       let hd = hd.insert_env(env, live);
                       let tl = tl.insert_env(env, live);
                       Cons(hd, tl).alloc(env)
                   }
               }
           }
        }

        impl<$short> HasNanodaDbg<$short> for List<$short, $base<$short>> {
            fn nanoda_dbg(self, ctx : &impl IsCtx<$short>) -> String {
                if self == Nil {
                    format!("[]")
                } else {
                    let mut acc = format!("[");
                    let mut cursor = self;
                    while let Cons(hd, tl) = cursor {
                        acc.push_str(hd.nanoda_dbg(ctx).as_str());
                        match tl.read(ctx) {
                            Nil => (),
                            Cons(..) => {
                            acc.push_str(", ");

                            }
                        }
                        cursor = tl.read(ctx);
                    }
                    acc.push(']');
                    acc
                }
            }
        }

        impl<$short> Ptr<$short, $base<$short>> {
            pub fn pos(
                self, 
                haystack : ListPtr<$short, $base<$short>>, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (Option<usize>, Step<PosZst>) {
                match haystack.read(ctx) {
                    Nil => {
                        Pos::BaseNone {
                            needle : self,
                            haystack,
                            pos : None,
                        }.step(ctx)
                    },
                    Cons(hd, tl) if hd == self => {
                        Pos::BaseSome {
                            needle : self,
                            haystack_tl : tl,
                            haystack,
                            pos : Some(0)
                        }.step(ctx)
                    }
                    Cons(x, tl) => {
                        let (pos, h1) = self.pos(tl, ctx);
                        let pos_prime = pos.map(|n| n + 1);
                        Pos::Step {
                            needle : self,
                            x,
                            haystack_tl : tl,
                            pos,
                            haystack,
                            pos_prime,
                            h1,
                        }.step(ctx)
                    }
                }
            }
        }
        
        impl<$short> ListPtr<$short, $base<$short>> {
 

            pub fn read(self, ctx : &impl IsCtx<$short>) -> List<$short, $base<$short>> {
                match self {
                    Ptr::E(index, h, z) => *ctx.env_store().$list_field.get_elem(index, h, z),
                    Ptr::L(index, h, z) => *ctx.live_store()
                                               .expect("Failed to get Live store! ListPtr")
                                               .$list_field
                                               .get_elem(index, h, z),
                    Ptr::P(index, h, z) => *ctx.pfinder_store()
                                               .expect("Failed to get pfinder store! ListPtr")
                                               .$list_field
                                               .get_elem(index, h, z)
                }
            }

            pub fn insert_env<$live, $env>(self, env : &mut Env<$env, impl $env + IsTracer>, live : &Store<$live, LiveZst>) -> ListPtr<$env, $base<$env>> {
                match self {
                    Ptr::E(index, _, z) => {
                        let underlying_data = self.read(env);
                        let p = env.store.$list_field.extend_safe(index, z);
                        assert_eq!(underlying_data, p.read(env));
                        p
                    },
                    Ptr::L(index, h, z) => {
                        live.$list_field.get_elem(index, h, z).insert_env(env, live)
                    },
                    Ptr::P(..) => unreachable!("P items hould never be put in the environment!")
                }
            }

             
            pub fn extend_lifetime<$env>(
                self,
                env : &mut Env<$env, impl $env + IsTracer>
            ) -> ListPtr<$env, $base<$env>> {
                match self {
                    Ptr::E(index, _, z) => {
                        let underlying_data = self.read(env);
                        let p = env.store.$list_field.extend_safe(index, z);
                        assert_eq!(underlying_data, p.read(env));
                        p
                    },
                    _ => unreachable!("Can only `extend_lifetime()` for environment items!")
                }
            }                     

            // tests `self is a subset of other`
            pub fn subset(self, super_ : ListPtr<$short, $base>, ctx : &mut impl IsLiveCtx<$short>) -> (bool, Step<IsSubsetZst>) {
                match self.read(ctx) {
                    Nil => {
                        IsSubset::BaseNil {
                            super_,
                            sub : self,
                            result : true,
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (maybe_pos, h1) = hd.pos(super_, ctx);
                        let (result, h2) = tl.subset(super_, ctx);
                        let result_prime = maybe_pos.is_some() && result;
                        IsSubset::Step {
                            hd,
                            maybe_pos,
                            sub : tl,
                            super_,
                            result,
                            sub_prime : self,
                            result_prime,
                            h1,
                            h2,
                        }.step(ctx)
                    }
                }
            }            

            pub fn skip(self, n : usize, ctx : &impl IsLiveCtx<$short>) -> ListPtr<$short, $base<$short>> {
                match self.read(ctx) {
                    _ if n == 0 => self,
                    Nil => self,
                    Cons(_, tl) => tl.skip(n - 1, ctx)
                }
            }
        
            pub fn take(self, n : usize, ctx : &mut impl IsLiveCtx<$short>) -> ListPtr<$short, $base<$short>> {
                match self.read(ctx) {
                    _ if n == 0 => Nil::<$base>.alloc(ctx),
                    Nil => Nil::<$base>.alloc(ctx),
                    Cons(hd, tl) => Cons(hd, tl.take(n - 1, ctx)).alloc(ctx)
                }
            }            

            // only used as an assertion.
            pub fn no_dupes(
                self, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (bool, Step<NoDupesZst>) {
                match self.read(ctx) {
                    Nil => {
                        NoDupes::BaseNil {
                            l : self,
                            result : true,
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (maybe_pos, h1) = hd.pos(tl, ctx);
                        assert!(maybe_pos.is_none());
                        let (b, h2) = tl.no_dupes(ctx);
                        NoDupes::StepTt {
                            hd,
                            tl,
                            l : self,
                            h1,
                            h2,
                            result  : (maybe_pos.is_none() && b),
                        }.step(ctx)
                    }
                }
            }            

            pub fn get(self, n : usize, ctx : &impl IsLiveCtx<$short>) -> Option<Ptr<$short, $base<$short>>> {
                match self.read(ctx) {
                    Nil => None,
                    Cons(hd, _) if n == 0 => Some(hd),
                    Cons(_, tl) => tl.get(n - 1, ctx)
                }
            }     

            pub fn len(self, ctx : &impl IsCtx<$short>) -> usize {
                match self.read(ctx) {
                    Nil => 0,
                    Cons(_, tl) => 1 + tl.len(ctx)
                }
            }

            pub fn concat(self, other : ListPtr<$short, $base<$short>>, ctx : &mut impl IsCtx<$short>) -> ListPtr<$short, $base<$short>> {
                match self.read(ctx) {
                    Nil => other,
                    Cons(hd, tl) => {
                        let sink = tl.concat(other, ctx);
                        Cons(hd, sink).alloc(ctx)
                    }
                }
            }

        }

        impl<$short> HasNanodaDbg<$short> for ListPtr<$short, $base<$short>> {
            fn nanoda_dbg(self, ctx : &impl IsCtx<$short>) -> String {
                self.read(ctx).nanoda_dbg(ctx)
            }
        }        
    };
}


#[macro_export]
macro_rules! arrow {
    ( [$dom:expr, $body:expr], $ctx:expr ) => {
        {
            <ExprPtr>::new_pi(Anon.alloc($ctx), $dom, BinderStyle::Default, $body, $ctx)
        }
    };
    ( [$dom:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let inner = arrow!([$($tl),*], $ctx);
            <ExprPtr>::new_pi(Anon.alloc($ctx), $dom, BinderStyle::Default, inner, $ctx)
        }
    }
}

#[macro_export]
macro_rules! fold_pis {
    ( [$dom:expr, $body:expr], $ctx:expr ) => {
        {
            $dom.apply_pi($body, $ctx).0
        }
    };
    ( [$dom:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let inner = fold_pis!([$($tl),*], $ctx);
            $dom.apply_pi(inner, $ctx).0
        }
    }
}

#[macro_export]
macro_rules! app {
    ( [$fun:expr, $arg:expr], $ctx:expr ) => {
        {
            $fun.new_app($arg, $ctx)
        }
    };
    ( [$fun:expr, $arg:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let mut base = $fun.new_app($arg, $ctx);
            $(
                base = base.new_app($tl, $ctx);
            )*
            base
        }
    }
}


#[macro_export]
macro_rules! name {
    ( $ctx:expr ) => { Name::Anon.alloc($ctx) };

    ([$($tl:expr),*], $ctx:expr) => {
        {
            let mut base = Anon.alloc($ctx);
            $(
                if let Ok(digit) = $tl.parse::<u64>() {
                    base = base.new_num(digit, $ctx);
                } else {
                    base = base.new_str($tl.to_string(), $ctx)
                }
            )*

            base
        }
    };
    ( $hd:expr, $ctx:expr ) => {
        if let Ok(digit) = $hd.parse::<u64>() {
            name!($ctx).new_num(digit, $ctx)
        } else {
            name!($ctx).new_str($hd.to_string(), $ctx)
        }
    };    
}

#[macro_export]
macro_rules! names {
    ( $ctx:expr ) => { List::Nil::<Name>.alloc($ctx) };
    ( [], $ctx:expr ) => { List::Nil::<Name>.alloc($ctx) };
    ( [$hd:expr], $ctx:expr ) => {
        List::Cons($hd, names!($ctx)).alloc($ctx)
    };
    ([$hd:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let tl = names!([$($tl),*], $ctx);
            List::Cons($hd, tl).alloc($ctx)
        }
    };
}

#[macro_export]
macro_rules! levels {
    ( $ctx:expr ) => { List::Nil::<Level>.alloc($ctx) };
    ( [], $ctx:expr ) => { List::Nil::<Level>.alloc($ctx) };
    ( [$hd:expr], $ctx:expr ) => {
        List::Cons($hd, levels!($ctx)).alloc($ctx)
    };
    ([$hd:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let tl = levels!([$($tl),*], $ctx);
            List::Cons($hd, tl).alloc($ctx)
        }
    };
}

#[macro_export]
macro_rules! exprs {
    ( $ctx:expr ) => { List::Nil::<Expr>.alloc($ctx) };
    ( [], $ctx:expr ) => { List::Nil::<Expr>.alloc($ctx) };
    ( [$hd:expr], $ctx:expr ) => {
        List::Cons($hd, exprs!($ctx)).alloc($ctx)
    };
    ([$hd:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let tl = exprs!([$($tl),*], $ctx);
            List::Cons($hd, tl).alloc($ctx)
        }
    };
}

#[macro_export]
macro_rules! param {
    ( [], $ctx:expr ) => {
        List::Nil::<Level>.alloc($ctx)
    };

    ( [$hd:expr], $ctx:expr ) => {
        List::Cons(param!($hd, $ctx), param!([], $ctx)).alloc($ctx)
    };
    ([$hd:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let tl : LevelsPtr = param!([$($tl),*], $ctx);
            List::Cons(param!($hd, $ctx), tl).alloc($ctx)
        }
    };
    ( $s:expr, $ctx:expr ) => {
        {
            Name::Anon.alloc($ctx)
            .new_str(String::from($s), $ctx)
            .new_param($ctx)
        }
    };    
}

#[macro_export]
macro_rules! sort {
    ( [$s:expr], $ctx:expr ) => {
        {
            Cons(sort!($s, $ctx), Nil.alloc($ctx)).alloc($ctx)
        }
    };
    ( $s:expr, $ctx:expr ) => {
        {
            param!($s, $ctx).new_sort($ctx)
        }
    };
}


#[macro_export]
macro_rules! ret_none_if {
    ( $e:expr ) => {
            if $e {
                return None
            }
    }
}


// We need to skip the 0th element of name and level
// to not re-print Anon/Zero, as well as the 0th
#[macro_export]
macro_rules! trace_env {
    ( $env:expr, $field:ident, $list_field:ident, $skip:literal ) => {
        {
            let len = $env.store.$field.elems.len();
            let start_idx = if $skip { 1usize } else { 0usize };
            for i in start_idx..len {
                let ptr = $env.store.$field.retrieve(i);
                ptr.trace_item($env);
            }
        }

        {
            let len = $env.store.$list_field.elems.len();
            for i in 1..len {
                let ptr = $env.store.$list_field.retrieve(i);
                ptr.trace_item($env);

            }
        }
    };
}

pub trait HasNanodaDbg<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String;
}


