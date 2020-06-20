use std::fs::File;
use std::io::BufWriter;
use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::{ Hash, BuildHasherDefault };
use std::marker::PhantomData;
use std::io::Result as IoResult;

use rustc_hash::FxHasher;
use indexmap::{ IndexMap, IndexSet };

use crate::name::{ NamePtr, Name, Name::* };
use crate::level::{ LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, Expr, LocalSerial };
use crate::env::{ Declar, RecRule, Notation, RecRulePtr, DeclarPtr, RecRulesPtr, DeclarsPtr };
use crate::tc::infer::InferFlag;
use crate::{ arena_item, has_list };
use crate::trace::items::HasTraceItem;
use crate::trace::{ IsTracer, TraceMgr };
use crate::trace::steps::*;


pub type FxIndexSet<A> = IndexSet<A, BuildHasherDefault<FxHasher>>;
pub type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

use List::*;

fn try_succ<'a>(op_n : Option<usize>, ctx : &mut impl IsCtx<'a>) -> (Option<usize>, Step<TrySucc>) {
    match op_n {
        None => {
            TrySucc::BaseNone {
                ind_arg1 : op_n,
                ind_arg2 : None
            }.step(ctx)
        },
        Some(n) => {
            TrySucc::BaseSome {
                n,
                ind_arg1 : op_n,
                ind_arg2 : Some(n + 1)
            }.step(ctx)
        }
    }
}

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

    fn insert_elem(&mut self, elem : A) -> Ptr<'a, A> {
        let (idx, _) = self.elems.insert_full(elem);
        self.marker.mk_ptr(idx)
    }

    fn check_dupe(&self, elem : &A) -> Option<Ptr<'a, A>> {
        self.elems
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
    pub abstr_cache  : FxIndexMap<(ExprPtr<'a>, u16), (ExprPtr<'a>, Step<AbstrAux<'a>>)>,
    pub inst_cache   : FxIndexMap<(ExprPtr<'a>, u16), (ExprPtr<'a>, Step<InstAux<'a>>)>,
    pub subst_cache   : FxIndexMap<(ExprPtr<'a>, LevelsPtr<'a>, LevelsPtr<'a>), (ExprPtr<'a>, Step<SubstE<'a>>)>,
    pub height_cache  : FxIndexMap<ExprPtr<'a>, (u16, Step<CalcHeight<'a>>)>,
    pub find_cache    : FxIndexMap<ExprPtr<'a>, (bool, Step<HasIndOcc<'a>>)>,
}

pub fn new_map<K : Hash + Eq, V>() -> FxHashMap<K, V> {
    FxHashMap::with_hasher(Default::default())
}

impl<'a, Z> ExprCache<'a, Z> {
    pub fn new() -> Self {
        ExprCache {
            marker : PhantomData,
            abstr_cache    : FxIndexMap::with_hasher(Default::default()),
            inst_cache     : FxIndexMap::with_hasher(Default::default()),
            subst_cache    : FxIndexMap::with_hasher(Default::default()),
            height_cache   : FxIndexMap::with_hasher(Default::default()),
            find_cache     : FxIndexMap::with_hasher(Default::default()),            
        }
    }
}

pub struct TcCache<'a> {
    infer_cache : FxHashMap<(ExprPtr<'a>, InferFlag), (ExprPtr<'a>, Step<Infer<'a>>)>,
    eq_cache    : FxHashMap<(ExprPtr<'a>, ExprPtr<'a>), Step<DefEq<'a>>>,
    whnf_cache  : FxHashMap<ExprPtr<'a>, (ExprPtr<'a>, Step<Whnf<'a>>)>,
}

impl<'a> TcCache<'a> {
    fn new() -> Self {
        TcCache {
            infer_cache : FxHashMap::with_hasher(Default::default()),
            eq_cache    : FxHashMap::with_hasher(Default::default()),
            whnf_cache  : FxHashMap::with_hasher(Default::default()),
        }
    }

    fn clear(&mut self) {
        self.eq_cache.clear();
        self.infer_cache.clear();
        self.whnf_cache.clear();
    }

}


pub struct PfinderCache<'a> {
    infer_cache : FxIndexMap<(ExprPtr<'a>, InferFlag), (ExprPtr<'a>, Step<Infer<'a>>)>,
    eq_cache    : FxIndexMap<(ExprPtr<'a>, ExprPtr<'a>), Step<DefEq<'a>>>,
    //ne_cache : FxHashSet<(ExprPtr<'a>, ExprPtr<'a>)>,
    whnf_cache  : FxIndexMap<ExprPtr<'a>, (ExprPtr<'a>, Step<Whnf<'a>>)>,
}


impl<'a> PfinderCache<'a> {
    fn new() -> Self {
        PfinderCache {
            infer_cache : FxIndexMap::with_hasher(Default::default()),
            eq_cache    : FxIndexMap::with_hasher(Default::default()),
            whnf_cache  : FxIndexMap::with_hasher(Default::default()),
        }
    }
    
    fn is_empty(&self) -> bool {
        self.eq_cache.is_empty() && self.infer_cache.is_empty() && self.whnf_cache.is_empty()
    }
}

pub struct Cache<'a, Z> {
    marker : PhantomData<Z>,
    expr_cache : ExprCache<'a, Z>,
    tc_cache : PfinderCache<'a>
}


impl<'a, Z> Cache<'a, Z> {
    pub fn new() -> Self {
        Self {
            marker : Default::default(),
            expr_cache : ExprCache::new(),
            tc_cache : PfinderCache::new(),
        }
    }

}

impl<'a> Cache<'a, PfinderZst> {
    pub fn get_snapshot(&self) -> Snapshot {
        Snapshot {
            abstr_cache_len  : self.expr_cache.abstr_cache.len(),
            inst_cache_len   : self.expr_cache.inst_cache.len(),
            subst_cache_len  : self.expr_cache.subst_cache.len(),
            height_cache_len : self.expr_cache.height_cache.len(),
            find_cache_len   : self.expr_cache.find_cache.len(),
            infer_cache_len  : self.tc_cache.infer_cache.len(),
            eq_cache_len     : self.tc_cache.eq_cache.len(),
            whnf_cache_len   : self.tc_cache.whnf_cache.len(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Snapshot {
    abstr_cache_len  : usize,
    inst_cache_len   : usize,
    subst_cache_len  : usize,
    height_cache_len : usize,
    find_cache_len   : usize,
    infer_cache_len  : usize,
    eq_cache_len     : usize,
    whnf_cache_len   : usize,
}
//#[derive(Debug)]
pub struct Env<'e, T : IsTracer> {
    pub store : Store<'e, EnvZst>,
    pub declars : FxIndexMap<NamePtr<'e>, (DeclarPtr<'e>, Step<AdmitDeclar<'e>>)>,
    pub notations : FxHashMap<NamePtr<'e>, Notation<'e>>,
    pub next_local : u64,
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
            next_local : 0u64,
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
            tc_cache : TcCache::new(),
            pfinder_store : Store::new(),
            pfinder_cache : Cache::new(),
        }
    }
}

pub struct Live<'l, 'e : 'l, T : IsTracer> {
    pub env : &'l mut Env<'e, T>,
    pub store : Store<'l, LiveZst>,
    expr_cache : ExprCache<'l, LiveZst>,
    tc_cache : TcCache<'l>,
    pfinder_store : Store<'l, PfinderZst>,
    pfinder_cache : Cache<'l, PfinderZst>,
}

impl<'t, 'l : 't, 'e : 'l, T> Live<'l, 'e, T> 
where T : 'e + IsTracer {
    pub fn as_tc(&'t mut self, dec_uparams : Option<LevelsPtr<'l>>, safe_only : Option<bool>) -> Tc<'t, 'l, 'e, T> {
        self.tc_cache.clear();
        assert!(self.pfinder_cache.tc_cache.is_empty());
        let dec_uparams = dec_uparams.unwrap_or_else(|| Nil::<Level>.alloc(self));

        Tc {
            live : self,
            dec_uparams,
            safe_only : safe_only.unwrap_or(false)
        }
    }

    //pub fn admit_declar(&mut self, d : Declar<'l>) {
    //    assert!(self.env.declars.get(&d.name()).is_none());
    //    let d = d.insert_env(self.env, &self.store).read(self.env);
    //    self.env.declars.insert(d.name(), d);
    //}
}

pub struct Tc<'t, 'l : 't, 'e : 'l, T : IsTracer> {
    live : &'t mut Live<'l, 'e, T>,
    dec_uparams : LevelsPtr<'l>,
    safe_only : bool,
}

pub struct Pfinder<'t, 'l : 't, 'e : 'l, T : IsTracer> {
    live : &'t mut Live<'l, 'e, T>,
    dec_uparams : LevelsPtr<'l>,
    safe_only : bool,
    snapshot : Snapshot
}

impl<'t, 'l : 't, 'e : 'l, T> Pfinder<'t, 'l, 'e, T>
where T : 'l + IsTracer {
    pub fn restore_snapshot(&mut self) {
        fn restore_aux<K : Hash + Eq, V>(map : &mut FxIndexMap<K, V>, target : usize) {
            while map.len() > target {
                map.pop();
            }
        }

        restore_aux(&mut self.live.pfinder_cache.expr_cache.abstr_cache, self.snapshot.abstr_cache_len);
        restore_aux(&mut self.live.pfinder_cache.expr_cache.inst_cache, self.snapshot.inst_cache_len);
        restore_aux(&mut self.live.pfinder_cache.expr_cache.subst_cache, self.snapshot.subst_cache_len);
        restore_aux(&mut self.live.pfinder_cache.expr_cache.height_cache, self.snapshot.height_cache_len);
        restore_aux(&mut self.live.pfinder_cache.expr_cache.find_cache, self.snapshot.find_cache_len);
        restore_aux(&mut self.live.pfinder_cache.tc_cache.infer_cache, self.snapshot.infer_cache_len);
        restore_aux(&mut self.live.pfinder_cache.tc_cache.eq_cache, self.snapshot.eq_cache_len);
        restore_aux(&mut self.live.pfinder_cache.tc_cache.whnf_cache, self.snapshot.whnf_cache_len);
    }


}

pub trait IsTc<'t, 'l : 't, 'e : 'l> : IsLiveCtx<'l> {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 'l, 'e, Self::Tracer>;
    fn safe_only(&self) -> bool;
    fn dec_uparams(&self) -> LevelsPtr<'l>;
    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)>;

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<Infer<'l>>)>;
    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<Step<DefEq<'l>>>;
    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<Whnf<'l>>)>;

    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : ExprPtr<'l>, step : Step<Infer<'l>>);
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, step : Step<DefEq<'l>>);
    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : ExprPtr<'l>, step : Step<Whnf<'l>>);
}

impl<'t, 'l : 't, 'e : 'l, T> IsTc<'t, 'l, 'e> for Tc<'t, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 'l, 'e, Self::Tracer> {
        let snapshot = self.live.pfinder_cache.get_snapshot();
        Pfinder {
            live : self.live,
            dec_uparams : self.dec_uparams,
            safe_only : self.safe_only,
            snapshot
        }
    }
    
    fn safe_only(&self) -> bool {
        self.safe_only
    }

    fn dec_uparams(&self) -> LevelsPtr<'l> {
        self.dec_uparams
    }

    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)> {
        Some((self.live.env.quot_mk?,
              self.live.env.quot_lift?,
              self.live.env.quot_ind?))
    }

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<Infer<'l>>)> {
        self.live.tc_cache.infer_cache.get(&(k, flag)).copied()
    }

    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<Step<DefEq<'l>>> {
        self.live.tc_cache.eq_cache.get(&(l, r)).copied()
    }

    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<Whnf<'l>>)> {
        self.live.tc_cache.whnf_cache.get(k).copied()
    }

    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : ExprPtr<'l>, step : Step<Infer<'l>>) {
        // the idx no longer comes from here.
        //let this_step_idx = self.mut_mgr().next_step_idx();
        self.live.tc_cache.infer_cache.insert((k, flag), (v, step));

    }
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, step : Step<DefEq<'l>>) {
        self.live.tc_cache.eq_cache.insert((l, r), step);
    }
    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : ExprPtr<'l>, step : Step<Whnf<'l>>) {
        self.live.tc_cache.whnf_cache.insert(k, (v, step));
    }
}

impl<'t, 'l : 't, 'e : 'l, T> IsTc<'t, 'l, 'e> for Pfinder<'t, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn as_pfinder<'sh, 'lo : 'sh>(&'lo mut self) -> Pfinder<'sh, 'l, 'e, T> {
        let snapshot = self.live.pfinder_cache.get_snapshot();
        Pfinder {
            live : self.live,
            dec_uparams : self.dec_uparams,
            safe_only : self.safe_only,
            snapshot
        }
    }
    
    fn safe_only(&self) -> bool {
        self.safe_only
    }

    fn dec_uparams(&self) -> LevelsPtr<'l> {
        self.dec_uparams
    }

    fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)> {
        Some((self.live.env.quot_mk?,
              self.live.env.quot_lift?,
              self.live.env.quot_ind?))
    }    

    fn check_infer_cache(&self, k : ExprPtr<'l>, flag : InferFlag) -> Option<(ExprPtr<'l>, Step<Infer<'l>>)> {
        self.live.tc_cache.infer_cache.get(&(k, flag))
        .or_else(|| self.live.pfinder_cache.tc_cache.infer_cache.get(&(k, flag)))
        .copied()
    }

    fn check_eq_cache(&self, l : ExprPtr<'l>, r : ExprPtr<'l>) -> Option<Step<DefEq<'l>>> {
        self.live.tc_cache.eq_cache.get(&(l, r))
        .or_else(|| self.live.pfinder_cache.tc_cache.eq_cache.get(&(l, r)))
        .copied()
    }

    fn check_whnf_cache(&self, k : &ExprPtr<'l>) -> Option<(ExprPtr<'l>, Step<Whnf<'l>>)> {
        self.live.tc_cache.whnf_cache.get(k)
        .or_else(|| self.live.pfinder_cache.tc_cache.whnf_cache.get(k))
        .copied()
    }
    
    fn insert_infer_cache(&mut self, k : ExprPtr<'l>, flag : InferFlag, v : ExprPtr<'l>, step : Step<Infer<'l>>) {
        self.live.pfinder_cache.tc_cache.infer_cache.insert((k, flag), (v, step));

    }
    fn insert_eq_cache(&mut self, l : ExprPtr<'l>, r : ExprPtr<'l>, step : Step<DefEq<'l>>) {
        self.live.pfinder_cache.tc_cache.eq_cache.insert((l, r), step);
    }

    fn insert_whnf_cache(&mut self, k : ExprPtr<'l>, v : ExprPtr<'l>, step : Step<Whnf<'l>>) {
        self.live.pfinder_cache.tc_cache.whnf_cache.insert(k, (v, step));
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
    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'a>, Step<AdmitDeclar<'a>>)>;
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer>;
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

    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'e>, Step<AdmitDeclar<'e>>)> {
        self.declars.get(&n).copied()
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

    
    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclar<'l>>)> {
        self.env.declars.get(&n).copied()
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

    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclar<'l>>)> {
        self.live.env.declars.get(&n).copied()
    }
    
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        self.live.mut_mgr()
    }
}

impl<'t, 'l : 't, 'e : 'l, T> IsCtx<'l> for Pfinder<'t, 'l, 'e, T>
where T : 'l + IsTracer {
    type Writable = PfinderZst;
    type Tracer = T;
    const IS_PFINDER : bool = true;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        &self.live.env.store
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        Some(&self.live.store)
    }

    fn pfinder_store(&self) -> Option<&Store<'l, PfinderZst>> {
        Some(&self.live.pfinder_store)
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        &mut self.live.pfinder_store
    }


    fn get_declar(&self, n : NamePtr) -> Option<(DeclarPtr<'l>, Step<AdmitDeclar<'l>>)> {
        self.live.env.declars.get(&n).copied()
    }
    
    fn mut_mgr(&mut self) -> &mut TraceMgr<Self::Tracer> {
        self.live.mut_mgr()
    }
}


// Gives access to expression caches.
pub trait IsLiveCtx<'a> : IsCtx<'a> {
    fn expr_cache(&mut self) -> &mut ExprCache<'a, Self::Writable>;
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

impl<'t, 'l : 't, 'e : 'l, T> IsLiveCtx<'l> for Pfinder<'t, 'l, 'e, T> 
where T : 'l + IsTracer {
    fn expr_cache(&mut self) -> &mut ExprCache<'l, PfinderZst> {
        &mut self.live.pfinder_cache.expr_cache
    }
    
    fn next_local(&mut self) -> LocalSerial {
        self.live.next_local()
    }
}

// Strings are a pain since they're the only type we deal with
// that isn't copy.
pub fn alloc_str<'a>(s : String, ctx : &mut impl IsCtx<'a>) -> Ptr<'a, String> {
    let r = if let Some(dupe_ptr) = ctx.env_store().strings.check_dupe(&s)
                            .or_else(|| ctx.live_store().and_then(|st| st.strings.check_dupe(&s))) {
        dupe_ptr
    } else {
        let r = ctx.mut_store().strings.insert_elem(s);
        r.trace_item(ctx);
        r

    };
    r
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
                        //if tl.len(ctx) != 0 {
                            acc.push_str(", ");
                        //}
                        cursor = tl.read(ctx);
                    }
                    acc.push(']');
                    acc
                }
            }
        }

        impl<$short> Ptr<$short, $base<$short>> {
            pub fn mem(
                self, 
                haystack : ListPtr<$short, $base<$short>>, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (bool, Step<Mem<$short, $base<$short>>>) {
                match haystack.read(ctx) {
                    Nil => {
                        Mem::BaseFf {
                            needle : self,
                            ind_arg2 : haystack,
                            ind_arg3 : false
                        }.step(ctx)
                    },
                    Cons(hd, tl) if self == hd => {
                        Mem::BaseTt {
                            needle : self,
                            tl : tl,
                            ind_arg2 : haystack,
                            ind_arg3 : true
                        }.step(ctx)
                    },
                    Cons(hd, tl) => {
                        let result = self == hd;
                        assert!(!result);
                        let (is_mem_rec, h1) = self.mem(tl, ctx);
                        Mem::Step {
                            needle : self,
                            x : hd,
                            tl : tl,
                            bl : is_mem_rec,
                            h1,
                            ind_arg2 : haystack,
                            ind_arg3 : (result || is_mem_rec)
                        }.step(ctx)
                    }
                }
            }        

            pub fn pos (
                self, 
                haystack : ListPtr<$short, $base<$short>>, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (Option<usize>, Step<Pos<$short, $base<$short>>>) {
                match haystack.read(ctx) {
                    Nil => {
                        Pos::BaseNone {
                            needle : self,
                            ind_arg2 : haystack,
                            ind_arg3 : None,
                        }.step(ctx)
                    }
                    Cons(hd, tl) if hd == self => {
                        Pos::BaseSome {
                            needle : self,
                            tl,
                            ind_arg2 : haystack,
                            ind_arg3 : Some(0)
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (n, h1) = self.pos(tl, ctx);
                        let (n_prime, h2) = try_succ(n, ctx);
                        Pos::Step {
                            needle : self,
                            x : hd,
                            tl,
                            n,
                            n_prime,
                            h1,
                            h2,
                            ind_arg2 : haystack,
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

            // tests `self is a subset of other`
            pub fn subset(self, super_ : ListPtr<$short, $base>, ctx : &mut impl IsLiveCtx<$short>) -> (bool, Step<IsSubset<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        IsSubset::BaseNil {
                            super_,
                            ind_arg1 : self,
                            ind_arg3 : true,
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (b1, h1) = hd.mem(super_, ctx);
                        let (b2, h2) = tl.subset(super_, ctx);
                        IsSubset::Step {
                            hd,
                            sub : tl,
                            super_,
                            b1,
                            b2,
                            h1,
                            h2,
                            ind_arg1 : self,
                            ind_arg3 : b1 && b2
                        }.step(ctx)
                    }
                }
            }            

            pub fn skip(
                self, 
                n : usize, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (ListPtr<$short, $base<$short>>, Step<Skip<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        Skip::BaseNil {
                            n,
                            ind_arg1 : self,
                        }.step(ctx)
                    },
                    _ if n == 0 => {
                        Skip::BaseZero {
                            l : self,
                            ind_arg2 : n,
                        }.step(ctx)
                    },
                    Cons(hd, tl) => {
                        let n_prime = (n - 1);
                        let (l_prime, h1) = tl.skip(n_prime, ctx);
                        Skip::Step {
                            hd,
                            tl,
                            l_prime,
                            n_prime,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : n,
                        }.step(ctx)
                    }
                }
            }
        
            pub fn take(
                self, 
                n : usize, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (ListPtr<$short, $base<$short>>, Step<Take<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        Take::BaseNil {
                            n,
                            ind_arg1 : self,
                        }.step(ctx)
                    },
                    Cons(hd, tl) if n == 0 => {
                        Take::BaseZero {
                            l : self,
                            ind_arg2 : n,
                            ind_arg3 : Nil::<$base>.alloc(ctx),
                        }.step(ctx)
                    },
                    Cons(hd, tl) => {
                        let n_prime = (n - 1);
                        let (l_prime, h1) = tl.take(n_prime, ctx);
                        let ind_arg3 = Cons(hd, l_prime).alloc(ctx);
                        Take::Step {
                            hd,
                            tl,
                            l_prime,
                            n_prime,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : n,
                            ind_arg3
                        }.step(ctx)
                    }
                }
            }            

            pub fn no_dupes(
                self, 
                ctx : &mut impl IsLiveCtx<$short>
            ) -> (bool, Step<NoDupes<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        NoDupes::BaseNil {
                            ind_arg1 : self,
                            ind_arg2 : true,
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (b1, h1) = hd.mem(tl, ctx);
                        let (b2, h2) = tl.no_dupes(ctx);
                        NoDupes::StepTt {
                            hd,
                            tl,
                            b1,
                            b2,
                            h1,
                            h2,
                            ind_arg1 : self,
                            ind_arg2 : ((!b1) && b2),
                        }.step(ctx)
                    }
                }
            }            

        
            pub fn get(
                self, 
                n : usize, 
                ctx : &mut impl IsLiveCtx<$short>
                // eg. (Option<ExprPtr<'a>, Step<Get<ExprPtr<'a>>>)
            ) -> (Option<Ptr<$short, $base<$short>>>, Step<Get<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        Get::BaseNil {
                            n,
                            ind_arg1 : self,
                            ind_arg3 : None
                        }.step(ctx)
                    },
                    Cons(hd, tl) if n == 0 => {
                        Get::BaseZero {
                            hd,
                            tl,
                            ind_arg1 : self,
                            ind_arg2 : n,
                            ind_arg3 : Some(hd)
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let n_prime = (n - 1);
                        let (out, h1) = tl.get(n_prime, ctx);
                        Get::Step {
                            hd,
                            tl,
                            n_prime,
                            out,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : n
                        }.step(ctx)
                    }
                }
            }            
            
            pub fn len(
                self, 
                ctx : &mut impl IsCtx<$short>
            ) -> (usize, Step<Len<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        Len::BaseNil {
                            ind_arg1 : self,
                            ind_arg2 : 0usize
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (n, h1) = tl.len(ctx);
                        Len::Step {
                            hd,
                            tl,
                            n,
                            h1,
                            ind_arg1 : self,
                            ind_arg2 : (1 + n)
                        }.step(ctx)
                    }
                }
            }

            pub fn concat(
                self, 
                other : ListPtr<$short, $base<$short>>,
                ctx : &mut impl IsCtx<$short>
            ) -> (ListPtr<$short, $base<$short>>, Step<Concat<$short, $base<$short>>>) {
                match self.read(ctx) {
                    Nil => {
                        Concat::BaseNil {
                            l2 : other,
                            ind_arg1 : self,
                        }.step(ctx)
                    }
                    Cons(hd, tl) => {
                        let (l2_prime, h1) = tl.concat(other, ctx);
                        let ind_arg3 = Cons(hd, l2_prime).alloc(ctx);
                        Concat::Step {
                            hd,
                            tl,
                            l2 : other,
                            l2_prime,
                            h1,
                            ind_arg1 : self,
                            ind_arg3
                        }.step(ctx)
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

//#[macro_export]
//macro_rules! trace_result {
//    ( $e:expr, $ctx:ident ) => {
//        let result = $e;
//        result.trace($ctx);
//        result
//    }
//}

pub trait HasNanodaDbg<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String;
}


