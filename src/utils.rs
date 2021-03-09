use std::convert::TryFrom;
use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::{ Hash, BuildHasherDefault };
use std::marker::PhantomData;

use indexmap::{ IndexSet, IndexMap };
use rustc_hash::FxHasher;


use crate::name::{ NamePtr, Name, Name::* };
use crate::level::{ LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, Expr, LocalSerial, BinderStyle };
use crate::env::{ Declar, RecRule, Notation };
use crate::tc::eq::ShortCircuit;
use crate::tc::infer::InferFlag;
use crate::{ arena_item, has_list };

use Live::*;

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

// We would really like to be able to just call this `Ptr` and use
// it as `X(usize, PhantomData<A>, XZst)`, but Rust's type 
// sytem can't figure out that the type parameter is only 
// used for PhantomData, so without the type alias that makes
// the PhantomData explicit, we can't make it copy while still
// pointing to strings. The alias works fine though, it doesn't
// end up causing any headaches elsewhere.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ptr2<PH> {
    E(u32, PH, EnvZst),
    L(u32, PH, LiveZst),
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
        match u32::try_from(index) {
            Ok(n) => Ptr::E(n, PhantomData, self),
            Err(..) => unreachable!("usize to u32 conv overflow in EnvZst::mk_ptr")
        }
    }
}

impl HasMkPtr for LiveZst {
    fn mk_ptr<'a, A>(self, index : usize) -> Ptr<'a, A> {
        match u32::try_from(index) {
            Ok(n) => Ptr::L(n, PhantomData, self),
            Err(..) => unreachable!("usize to u32 conv overflow in LiveZst::mk_ptr")
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum List<'a, A> {
    Nil,
    Cons(Ptr<'a, A>, ListPtr<'a, A>)
}


pub type ListPtr<'a, A> = Ptr<'a, List<'a, A>>;

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

    pub fn get_elem(&self, index : u32, _ : PhantomData<&'_ A>, _ : Z) -> &A {
        self.elems.get_index(index as usize).expect("Checked `None`")
    }

    pub fn extend_safe(&self, index : u32, _z : Z) -> Ptr<'a, A> {
        self.marker.mk_ptr(index as usize)
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
}

impl<'a, Z : HasMkPtr> Store<'a, Z> {
    pub fn new() -> Self {
        Store {
            strings        : Set::new(),
            names          : Set::new(),
            name_lists     : Set::new(),
            levels         : Set::new(),
            level_lists    : Set::new(),
            exprs          : Set::new(),
            expr_lists     : Set::new(),
            rec_rules      : Set::new(),
            rec_rule_lists : Set::new(),
        }
    }
}

pub struct ExprCache<'a> {
    pub abstr_cache   : FxHashMap<(ExprPtr<'a>, u16), ExprPtr<'a>>,
    pub inst_cache    : FxHashMap<(ExprPtr<'a>, u16), ExprPtr<'a>>,
    pub subst_cache   : FxHashMap<(ExprPtr<'a>, LevelsPtr<'a>, LevelsPtr<'a>), ExprPtr<'a>>,
    pub height_cache  : FxHashMap<ExprPtr<'a>, u16>,
    pub find_cache    : FxHashMap<ExprPtr<'a>, bool>,            
}

pub fn new_map<K : Hash + Eq, V>() -> FxHashMap<K, V> {
    FxHashMap::with_hasher(Default::default())
}

impl<'a> ExprCache<'a> {
    pub fn new() -> Self {
        ExprCache {
            abstr_cache    : FxHashMap::with_hasher(Default::default()),
            inst_cache     : FxHashMap::with_hasher(Default::default()),
            subst_cache    : FxHashMap::with_hasher(Default::default()),
            height_cache   : FxHashMap::with_hasher(Default::default()),
            find_cache     : FxHashMap::with_hasher(Default::default()),            
        }
    }
}

pub struct TcCache<'a> {
    pub eq_cache    : FxHashMap<(ExprPtr<'a>, ExprPtr<'a>), ShortCircuit>,
    pub infer_cache : FxHashMap<(ExprPtr<'a>, InferFlag), ExprPtr<'a>>,
    pub whnf_cache  : FxHashMap<ExprPtr<'a>, ExprPtr<'a>>,
}

impl<'a> TcCache<'a> {
    fn new() -> Self {
        TcCache {
            infer_cache : FxHashMap::with_hasher(Default::default()),
            eq_cache    : FxHashMap::with_hasher(Default::default()),
            whnf_cache  : FxHashMap::with_hasher(Default::default()),
        }
    }
}

//#[derive(Debug)]
pub struct Env<'e> {
    pub store : Store<'e, EnvZst>,
    pub declars : FxIndexMap<NamePtr<'e>, Declar<'e>>,
    pub notations : FxHashMap<NamePtr<'e>, Notation<'e>>,
    pub next_local : u64,
    pub quot_mk : Option<NamePtr<'e>>,
    pub quot_lift : Option<NamePtr<'e>>,
    pub quot_ind : Option<NamePtr<'e>>,
    pub debug_mode: bool
}

impl<'l, 'e : 'l> Env<'e> {
    pub fn new(debug_mode: bool) -> Self {
        let mut env = Env {
            store : Store::new(),
            declars : FxIndexMap::with_hasher(Default::default()),
            notations : FxHashMap::with_hasher(Default::default()),
            next_local : 0u64,
            quot_mk : None,
            quot_lift : None,
            quot_ind : None,
            debug_mode
        };

        Anon.alloc(&mut env);
        Zero.alloc(&mut env);
        Nil::<Name>.alloc(&mut env);
        Nil::<Level>.alloc(&mut env);
        Nil::<Expr>.alloc(&mut env);
        Nil::<RecRule>.alloc(&mut env);

        env
    }
    pub fn as_compiler(&'l mut self) -> Live<'l, 'e> {
        Compiler {
            env : self,
            store : Store::new(),
            cache : ExprCache::new(),
            next_local : 0u64,
        }
    }

    
    pub fn as_checker(&'l self) -> Live<'l, 'e> {
        Checker {
            env : self,
            store : Store::new(),
            cache : ExprCache::new(),
            next_local : 0u64,
        }
    }
}


pub enum Live<'l, 'e : 'l> {
    Compiler {
        env : &'l mut Env<'e>,
        store : Store<'l, LiveZst>,
        cache : ExprCache<'l>,
        next_local : u64,
    },
    Checker {
        env : &'l Env<'e>,
        store : Store<'l, LiveZst>,
        cache : ExprCache<'l>,
        next_local : u64,
    }
}

impl<'t, 'l : 't, 'e : 'l> Live<'l, 'e> {
    pub fn as_tc(
        &'t mut self, 
        dec_uparams : Option<LevelsPtr<'l>>, 
        safe_only : Option<bool>
    ) -> Tc<'t, 'l, 'e> {
        Tc {
            live : self,
            dec_uparams,
            safe_only : safe_only.unwrap_or(false),
            cache : TcCache::new(),
            local_cache : FxHashMap::with_hasher(Default::default())
        }
    }

    pub fn get_env(&self) -> &Env<'e> {
        match self {
            Compiler { env, .. } => env,
            Checker { env, .. } => env,
        }
    }

    pub fn mut_env(&mut self) -> &mut Env<'e> {
        match self {
            Compiler { env, .. } => env,
            _ => unreachable!("Cannot get mutable access to Env through a `Live::Checker`")
        }
    }


    pub fn admit_declar(&mut self, d : Declar<'l>) {
        match self {
            Compiler { env, store, .. } => {
                assert!(env.declars.get(&d.name()).is_none());
                let d = d.insert_env(env, &store);

                env.declars.insert(d.name(), d);                
            },
            _ => unreachable!("Cannot use a Live::Checker to admit a declaration!")
        }
    }    


}

pub struct Tc<'t, 'l : 't, 'e : 'l> {
    pub live : &'t mut Live<'l, 'e>,
    pub dec_uparams : Option<LevelsPtr<'l>>,
    pub safe_only : bool,
    pub cache : TcCache<'l>,
    local_cache : FxHashMap<ExprPtr<'l>, Vec<ExprPtr<'l>>>,
}

impl<'t, 'l : 't, 'e : 'l> Tc<'t, 'l, 'e> {
    pub fn quot_names(&self) -> Option<(NamePtr<'l>, NamePtr<'l>, NamePtr<'l>)> {
        Some((
            self.live.get_env().quot_mk?,
            self.live.get_env().quot_lift?,
            self.live.get_env().quot_ind?
        ))
    }    

    pub fn get_local(&mut self, n : NamePtr<'l>, t : ExprPtr<'l>, s : BinderStyle) -> ExprPtr<'l> {
        let out = self.local_cache.get_mut(&t).and_then(|v| v.pop());
        out.unwrap_or_else(|| <ExprPtr>::new_local(n, t, s, self))
    }

    pub fn replace_local(&mut self, l : ExprPtr<'l>) {
        match l.read(self) {
            Expr::Local { b_type, .. } =>  {
                match self.local_cache.get_mut(&b_type) {
                    Some(v) => { v.push(l); },
                    None => { self.local_cache.insert(b_type, vec![l]); }
                }
            },
            _ => unreachable!("Can't replace a non-local")
        }
    }      
}

pub trait IsCtx<'a> {
    type Writable : HasMkPtr;
    fn env_store(&self) -> &Store<'a, EnvZst>;
    fn live_store(&self) -> Option<&Store<'a, LiveZst>>;
    fn mut_store(&mut self) -> &mut Store<'a, Self::Writable>;
    fn get_declar(&self, n : &NamePtr) -> Option<Declar<'a>>;
    fn debug_mode(&self) -> bool;
}

impl<'e> IsCtx<'e> for Env<'e> {
    type Writable = EnvZst;

    fn env_store(&self) -> &Store<'e, EnvZst> {
        &self.store
    }

    fn live_store(&self) -> Option<&Store<'e, LiveZst>> {
        None
    }

    fn mut_store(&mut self) -> &mut Store<'e, Self::Writable> {
        &mut self.store
    }

    fn get_declar(&self, n : &NamePtr) -> Option<Declar<'e>> {
        self.declars.get(n).copied()
    }

    fn debug_mode(&self) -> bool {
        self.debug_mode
    }
}

impl<'l, 'e : 'l> IsCtx<'l> for Live<'l, 'e> {
    type Writable = LiveZst;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        match self {
            Compiler { env, .. } => &env.store,
            Checker { env, .. } => &env.store
        }
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        match self {
            Compiler { store, .. } => Some(&store),
            Checker { store, .. } => Some(&store)
        }
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        match self {
            Compiler { ref mut store, .. } => store,
            Checker { ref mut store, .. } => store
        }
    }

    fn get_declar(&self, n : &NamePtr) -> Option<Declar<'l>> {
        self.get_env().declars.get(n).copied()
    }

    fn debug_mode(&self) -> bool {
        match self {
            Live::Compiler { env, .. } => env.debug_mode(),
            Live::Checker { env, .. } => env.debug_mode()
        }
    }

}

impl<'t, 'l : 't, 'e : 'l> IsCtx<'l> for Tc<'t, 'l, 'e> {
    type Writable = LiveZst;

    fn env_store(&self) -> &Store<'l, EnvZst> {
        &self.live.env_store()
    }

    fn live_store(&self) -> Option<&Store<'l, LiveZst>> {
        self.live.live_store()
    }

    fn mut_store(&mut self) -> &mut Store<'l, Self::Writable> {
        self.live.mut_store()
    }

    fn get_declar(&self, n : &NamePtr) -> Option<Declar<'l>> {
        self.live.get_declar(n)
    }

    fn debug_mode(&self) -> bool {
        self.live.debug_mode()
    }
}

// Gives access to expression caches.
pub trait IsLiveCtx<'a> : IsCtx<'a> {
    fn expr_cache(&mut self) -> &mut ExprCache<'a>;
    fn next_local(&mut self) -> LocalSerial;
}


impl<'l, 'e : 'l> IsLiveCtx<'l> for Live<'l, 'e> {
    fn expr_cache(&mut self) -> &mut ExprCache<'l> {
        match self {
            Compiler { ref mut cache, .. } => cache,
            Checker { ref mut cache, .. } => cache,
        }
    }
    
    #[allow(unused_must_use)]
    fn next_local(&mut self) -> LocalSerial {
        match self {
            | Compiler { next_local, .. }
            | Checker { next_local, .. } => {
                let this_local = *next_local;
                std::mem::replace(next_local, *next_local + 1);
                LocalSerial(this_local)
            }
        }
    }
}

impl<'t, 'l : 't, 'e : 'l> IsLiveCtx<'l> for Tc<'t, 'l, 'e> {
    fn expr_cache(&mut self) -> &mut ExprCache<'l> {
        self.live.expr_cache()
    }
    
    fn next_local(&mut self) -> LocalSerial {
        self.live.next_local()
    }

}

// Strings are a pain since they're the only type we deal with
// that isn't copy.
pub fn alloc_str<'a>(s : String, ctx : &mut impl IsCtx<'a>) -> Ptr<'a, String> {
    if let Some(dupe_ptr) = ctx.env_store().strings.check_dupe(&s)
                            .or_else(|| ctx.live_store().and_then(|st| st.strings.check_dupe(&s))) {
        dupe_ptr
    } else {
        ctx.mut_store().strings.insert_elem(s)

    }
}

impl<'s, 'a : 's> Ptr<'a, String> {
    pub fn read(self, ctx : &'s impl IsCtx<'a>) -> &'s String {
        match self {
            Ptr::E(index, h, z) => &ctx.env_store().strings.get_elem(index, h, z),
            Ptr::L(index, h, z) => &ctx.live_store().expect("Strings failed to read live store!").strings.get_elem(index, h, z),
        }
    }
}


arena_item!{ 'a, 'e, 'l, Name, names }
arena_item!{ 'a, 'e, 'l, Level, levels }
arena_item!{ 'a, 'e, 'l, Expr, exprs }
arena_item!{ 'a, 'e, 'l, RecRule, rec_rules }
has_list!{ 'a, 'e, 'l, Name, name_lists }
has_list!{ 'a, 'e, 'l, Level, level_lists }
has_list!{ 'a, 'e, 'l, Expr, expr_lists }
has_list!{ 'a, 'e, 'l, RecRule, rec_rule_lists }

#[macro_export]
macro_rules! arena_item {
    ( $short:lifetime, $env:lifetime, $live:lifetime, $base:ident, $field:ident ) => {
        impl<$short> $base<$short> {
            pub fn check_dupe(self, ctx : &impl IsCtx<$short>) -> Option<Ptr<$short, $base<$short>>> {
                ctx.env_store().$field.check_dupe(&self)
                .or_else(|| ctx.live_store().and_then(|sto| sto.$field.check_dupe(&self)))
            }

            pub fn alloc(self, ctx : &mut impl IsCtx<$short>) -> Ptr<$short, $base<$short>> {
                if let Some(dupe_ptr) = self.check_dupe(ctx) {
                    dupe_ptr
                } else {
                    ctx.mut_store().$field.insert_elem(self)
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
                }
            }

            


            pub fn insert_env<$live, $env>(self, env : &mut Env<$env>, live : &Store<$live, LiveZst>) -> Ptr<$env, $base<$env>> {
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
                    ctx.mut_store().$list_field.insert_elem(self)
                }
            }            

            pub fn check_dupe(self, ctx : &impl IsCtx<$short>) -> Option<ListPtr<$short, $base<$short>>> {
                ctx.env_store().$list_field.check_dupe(&self)
                .or_else(|| ctx.live_store().and_then(|sto| sto.$list_field.check_dupe(&self)))
            }


           pub fn insert_env<$live, $env>(self, env : &mut Env<$env>, live : &Store<$live, LiveZst>) -> ListPtr<$env, $base<$env>> {
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
                        if tl.len(ctx) != 0 {
                            acc.push_str(", ");
                        }
                        cursor = tl.read(ctx);
                    }
                    acc.push(']');
                    acc
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
                }
            }

            pub fn insert_env<$live, $env>(self, env : &mut Env<$env>, live : &Store<$live, LiveZst>) -> ListPtr<$env, $base<$env>> {
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
                }
            }

            pub fn mem(self, elem : Ptr<$base>, ctx : &impl IsLiveCtx<$short>) -> bool {
                match self.read(ctx) {
                    Cons(hd, _) if hd == elem => true,
                    Cons(_, tl) => tl.mem(elem, ctx),
                    Nil => false
                }
            }             

            pub fn pos(self, elem : Ptr<$base>, ctx : &impl IsLiveCtx<$short>) -> Option<usize> {
                match self.read(ctx) {
                    Cons(hd, _) if hd == elem => Some(0),
                    Cons(_, tl) => tl.pos(elem, ctx).map(|n| n + 1),
                    Nil => None
                }
            }

            // tests `self is a subset of other`
            pub fn subset(self, other : ListPtr<$short, $base>, ctx : &mut impl IsLiveCtx<$short>) -> bool {
                match self.read(ctx) {
                    Cons(hd, tl) => other.mem(hd, ctx) && tl.subset(other, ctx),
                    _ => true,
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

            pub fn no_dupes(self, ctx : &impl IsLiveCtx<$short>) -> bool {
                match self.read(ctx) {
                    Nil => true,
                    Cons(hd, tl) => (!tl.mem(hd, ctx)) && (tl.no_dupes(ctx))
                }
            }            

            pub fn len(self, ctx : &impl IsCtx<$short>) -> usize {
                match self.read(ctx) {
                    Nil => 0,
                    Cons(_, tl) => 1 + tl.len(ctx)
                }
            }
        
            pub fn get(self, n : usize, ctx : &impl IsLiveCtx<$short>) -> Option<Ptr<$short, $base<$short>>> {
                match self.read(ctx) {
                    Nil => None,
                    Cons(hd, _) if n == 0 => Some(hd),
                    Cons(_, tl) => tl.get(n - 1, ctx)
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
            $dom.apply_pi($body, $ctx)
        }
    };
    ( [$dom:expr, $($tl:expr),*], $ctx:expr) => {
        {
            let inner = fold_pis!([$($tl),*], $ctx);
            $dom.apply_pi(inner, $ctx)
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
macro_rules! levels {
    ( $ctx:expr ) => { List::Nil::<Level>.alloc($ctx) };
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

pub trait HasNanodaDbg<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String;
}

