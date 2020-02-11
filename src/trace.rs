use indexmap::IndexSet;
use parking_lot::RwLock;
use std::sync::Arc;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::io::Result as IoResult;

use nanoda_macros::is_step;
use enum_tools::{ Get, GetMut, IterUnique };

use crate::env::{ ConstantBase, 
                  ConstantInfo, 
                  ConstantInfo::*, 
                  AxiomVal, 
                  DefinitionVal, 
                  TheoremVal, 
                  QuotVal, 
                  InductiveVal, 
                  ConstructorVal, 
                  OpaqueVal,
                  ReducibilityHint };
use crate::recursor::{ RecursorVal, RecursorRule };
use crate::name::{ Name, InnerName::*, mk_anon };
use crate::expr::{ Expr, InnerExpr::*, Binder, BinderStyle::* };
use crate::level::{ Level, InnerLevel::*, mk_zero };
use crate::utils::{ ShortCircuit, ShortCircuit::*, DeltaResult, Either, Either::* };
use crate::tc::{ Cheap, Cheap::* };
use crate::inductive::newinductive::{ InductiveType, Constructor };

use Step::*;
use ItemIdx::*;
use TraceItem::*;


pub static SAFETY_IDX_COUNTER : AtomicUsize = AtomicUsize::new(0);

pub type ArcBaseStorage = Arc<RwLock<BaseStorage>>;


// You can safely ignore anything to do with `safety idx`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SafetyIdx(usize);


impl SafetyIdx {
    pub fn from_usize(n : usize) -> Self {
        SafetyIdx(n)
    }

    pub fn to_usize(&self) -> usize {
        match self {
            SafetyIdx(n) => *n
        }
    }

}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct StepIdx(usize);

impl StepIdx {
    pub fn from_usize(n : usize) -> Self {
        StepIdx(n)
    }

    pub fn to_usize(&self) -> usize {
        match self {
            StepIdx(n) => *n
        }
    }
}

impl std::fmt::Display for StepIdx {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "${}", self.to_usize())
    }
}


// Having an enum with two variants lets us maintain a universal
// set and a forked set without having to later try and reason
// about offsets to figure out whether/where something exists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ItemIdx {
    UnivIdx(usize),
    ForkIdx(usize),
}

// when doing string interpolation with the `Display` formatter,
// show elements of the base set as their inner usize. Show elements
// of a forked set as their inner usize, but with a `!` prefix
impl std::fmt::Display for ItemIdx {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnivIdx(n) => write!(f, "*{}", n),
            ForkIdx(n) => write!(f, "!{}", n)
        }
    }
}


#[derive(Debug, Clone, Hash)]
pub struct StepInfo {
    self_idx : Option<StepIdx>,
    references : Vec<StepIdx>,
    safety_idx : SafetyIdx,
    result : Option<ItemIdx>,
    extras : Vec<String>
}

impl StepInfo {
    pub fn new(safety_idx : SafetyIdx) -> Self {
        StepInfo {
            self_idx : None,
            references : Vec::new(),
            safety_idx,
            result : None,
            extras : Vec::new(),
        }
    }
}

impl Step {
    pub fn get_self_idx(&self) -> &Option<StepIdx> {
        &(self.get_info().self_idx)
    }

    pub fn get_mut_self_idx(&mut self) -> &mut Option<StepIdx> {
        &mut (self.get_mut_info().self_idx)
    }

    pub fn get_extras(&self) -> &Vec<String> {
        &(self.get_info().extras)
    }

    pub fn get_mut_extras(&mut self) -> &mut Vec<String> {
        &mut (self.get_mut_info().extras)
    }

    pub fn get_result(&self) -> &Option<ItemIdx> {
        &(self.get_info().result)
    } 
    pub fn get_mut_result(&mut self) -> &mut Option<ItemIdx> {
        &mut (self.get_mut_info().result)
    } 

    pub fn get_mut_references(&mut self) -> &mut Vec<StepIdx> {
        &mut (self.get_mut_info().references)
    }
    
    pub fn get_references(&self) -> &Vec<StepIdx> {
        &(self.get_info().references)
    }

    pub fn get_mut_safety_idx(&mut self) -> &mut SafetyIdx {
        &mut (self.get_mut_info().safety_idx)
    }
    
    pub fn get_safety_idx(&self) -> &SafetyIdx {
        &(self.get_info().safety_idx)
    }

}


// self_idx : Option<StepIdx>,
// references : Vec<StepIdx>,
// result : Option<ItemIdx>,
// extras : Vec<String>
// safety_idx : SafetyIdx,
#[is_step] 
#[derive(Debug, Clone, Hash, Get, GetMut, IterUnique)]
pub enum Step {
    #[short(UDE)]
    UseDepElim {
        info : StepInfo,
        base_type : ItemIdx,
    },
    #[short(GRV)]
    GetRecursorVal {
        info : StepInfo,
        name : ItemIdx,
    },
    #[short(GRR)]
    GetRecRuleFor {
        info : StepInfo,
        constant_base : ItemIdx,
        major : ItemIdx,
    },
    #[short(GMI)]
    GetMajorIdx {
        info : StepInfo,
        constant_base : ItemIdx,
    },
    #[short(VIA)]
    IsValidIndApp {
        info : StepInfo,
    },
    #[short(VIA2)]
    IsValidIndApp2 {
        info : StepInfo,
    },
    #[short(DRS)]
    DeclareRecursors {
        info : StepInfo,
    },
    #[short(GAIN)]
    GetAllInductiveNames {
        info : StepInfo,
    },
    #[short(MRR)]
    MkRecRules {
        info : StepInfo,
    },
    #[short(CMP)]
    CollectMinorPremises {
        info : StepInfo,
    },
    #[short(CC)]
    CollectCs {
        info : StepInfo,
    },
    #[short(GRL)]
    GetRecLevels {
        info : StepInfo,
    },
    #[short(GRLP)]
    GetRecLparams {
        info : StepInfo,
    },
    #[short(GLPN)]
    GetRecLparamNames {
        info : StepInfo,
    },
    #[short(MRI)]
    MkRecInfos {
        info : StepInfo,
    },
    #[short(GI)]
    GetIIndices {
        info : StepInfo,
    },
    #[short(IKT)]
    InitKTarget {
        info : StepInfo,
    },
    #[short(IEL)]
    InitElimLevel {
        info : StepInfo,
    },
    #[short(EOZ)]
    ElimOnlyAtUniverseZero {
        info : StepInfo,
    },
    #[short(DCN)]
    DeclareConstructors {
        info : StepInfo,
    },
    #[short(CCN)]
    CheckConstructors {
        info : StepInfo,
    },
    #[short(CP)]
    CheckPositivity {
        info : StepInfo,
    },
    #[short(IRF)]
    IsReflexive {
        info : StepInfo,
    },
    #[short(IRA)]
    IsRecArgument {
        info : StepInfo,
    },
    #[short(NDN)]
    EnsureNotDupeName {
        info : StepInfo,
        name : ItemIdx,
    },
    #[short(DIT)]
    DeclareInductiveTypes {
        info : StepInfo,
    },
    #[short(AO)]
    AddOpaque {
        info : StepInfo,
        opaque : ItemIdx,
    },
    #[short(AM)]
    AddMutual {
        info : StepInfo,
        defns : ItemIdx,
    },
    #[short(AT)]
    AddTheorem {
        info : StepInfo,
        thm : ItemIdx,
    },
    #[short(NDL)]
    EnsureNoDupeLparams {
        info : StepInfo,
        v : ItemIdx,
    },
    #[short(AIC)]
    AddInductiveCore {
        info : StepInfo,
        name : ItemIdx,
        lparams : ItemIdx,
        types : ItemIdx,
    },
    #[short(AA)]
    AddAxiom {
        info : StepInfo,
        ax : ItemIdx,
    },
    #[short(AD)]
    AddDefinition {
        info : StepInfo,
        definition : ItemIdx,
    },
    #[short(AQ)]
    AddQuot {
        info : StepInfo,
        quot : ItemIdx,
    },
    #[short(CIT)]
    CheckInductiveTypes {
        info : StepInfo,
        types : ItemIdx,
    },
    #[short(CCB)]
    CheckConstantBase {
        info : StepInfo,
        constant_base : ItemIdx,
    },
    #[short(CT)]
    CheckType {
        info : StepInfo,
        val : ItemIdx,
        type_ : ItemIdx,
    },
    #[short(CI)]
    CheckedInfer {
        info : StepInfo,
        e : ItemIdx,
        levels : ItemIdx,
    },
    #[short(ICK)]
    InferThenCheckType {
        info : StepInfo,
        val : ItemIdx,
        type_ : ItemIdx,
    },
    #[short(UI)]
    UncheckedInfer {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(IT)]
    InferType {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(IS)]
    InferSort {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(ITC)]
    InferTypeCore {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(IL)]
    InferLambda {
        info : StepInfo,
        e : ItemIdx,
        infer_only : ItemIdx,
    },
    #[short(IC)]
    InferConst {
        info : StepInfo,
        n : ItemIdx,
        ls : ItemIdx,
    },
    #[short(IZ)]
    InferLet {
        info : StepInfo,
        binding : ItemIdx,
        val : ItemIdx,
        body : ItemIdx,
        infer_only : ItemIdx
    },
    #[short(IP)]
    InferPi {
        info : StepInfo,
        e : ItemIdx
    },
    #[short(IA)]
    InferApps {
        info : StepInfo,
        e : ItemIdx,
        infer_only : ItemIdx,
    },
    #[short(ET)]
    EnsureType {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(EP)]
    EnsurePi {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(EPC)]
    EnsurePiCore {
        info : StepInfo,
        e : ItemIdx,
    },
   
    #[short(ES)]
    EnsureSort {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(ESC)]
    EnsureSortCore {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(EQ)]
    CheckDefEq {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(EQC)]
    EqCore { 
        info : StepInfo,
        e1 : ItemIdx, 
        e2 : ItemIdx, 
    },
    #[short(QDE)]
    QuickDefEq { 
        info : StepInfo,
        e1 : ItemIdx, 
        e2 : ItemIdx, 
    },
    #[short(DEL)]
    DefEqLambdas {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(DEP)]
    DefEqPis {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(DEA)]
    DefEqApps {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(P)]
    IsProp {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(ISP)]
    IsProposition {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(ISPR)]
    IsProof {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(PIE)]
    ProofIrrelEq {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(ID)]
    IsDelta {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(UC)]
    UnfoldDefCore {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(UD)]
    UnfoldDef {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(UDI)]
    UnfoldDefInfallible {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(EA)]
    EqArgs {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(IDEA)]
    IsDefEqApp {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(LDR)]
    LazyDeltaReduction {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(IR)]
    IsRec {
        info : StepInfo,
    },
    #[short(LDS)]
    LazyDeltaReductionStep {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(W)]
    Whnf {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(WC)]
    WhnfCore {
        info : StepInfo,
        e : ItemIdx,
        cheap : ItemIdx,
    },
    #[short(WL)]
    WhnfLambda {
        info : StepInfo,
        e : ItemIdx,
        es : ItemIdx,
    },
    #[short(RQR)]
    ReduceQuotRec {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(RIR)]
    ReduceInductiveRec {
        info : StepInfo,
        e : ItemIdx,
        cheap : ItemIdx,
    },
    #[short(MNC)]
    MkNullaryCnstr {
        info : StepInfo,
        e : ItemIdx,
    },
    #[short(CK)]
    ToCnstrWhenK {
        info : StepInfo,
        e : ItemIdx, 
        rval : ItemIdx,
    },
    #[short(TEE)]
    TryEtaExpansion {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(TEEC)]
    TryEtaExpansionCore {
        info : StepInfo,
        e1 : ItemIdx,
        e2 : ItemIdx,
    },
    #[short(IN)]
    Instantiate {
        info : StepInfo,
        e : ItemIdx,
        substs : ItemIdx,
    },
    #[short(AB)]
    Abstract {
        info : StepInfo,
        e : ItemIdx,
        locals : ItemIdx,
    },
    #[short(ILP)]
    InstantiateLparams {
        info : StepInfo,
        e : ItemIdx,
        substs : ItemIdx,
    },
    #[short(SI)]
    Simplify {
        info : StepInfo,
        lvl : ItemIdx,
    },
    #[short(GEQ)]
    IsGeq {
        info : StepInfo,
        l1 : ItemIdx,
        l2 : ItemIdx,
    },
    #[short(ANTI)]
    EqByAntisymm {
        info : StepInfo,
        l1 : ItemIdx,
        l2 : ItemIdx,
    },
    #[short(ILS)]
    InstantiateLevel {
        info : StepInfo,
        l : ItemIdx,
        ls : ItemIdx
    },
    #[short(IVLP)]
    InstantiateValueLparam {
        info : StepInfo,
        const_info : ItemIdx,
        ls : ItemIdx,
    },
    #[short(CL)]
    CheckLevel {
        info : StepInfo,
        lparams : ItemIdx,
        l : ItemIdx,
    }
}

#[derive(Debug, Clone)]
pub struct TraceOptions {
    pub names : Vec<Name>,
    pub use_short_names : bool,
    pub omit_spaces : bool
}

impl TraceOptions {
    pub fn new(names : Vec<Name>,
               use_short_names : bool,
               omit_spaces : bool) -> Self {
        TraceOptions {
            names,
            use_short_names,
            omit_spaces
        }
    }
}

pub type ArcTraceMgr<T> = Arc<RwLock<TraceMgr<T>>>;

// Struct storing state that allows us to 
// make a navigable map out of the trace data. 
// a) `tracer : T` is anything implementing the `Tracer` trait,
// which defines how steps are actually handled. TracerMgr does all of the
// work of building a graph connecting the steps, and at the end calls
// `step.trace()` on each item in the graph, which is where your behavior
// will be executed.
// b) the stack is needed to allow us to properly relate steps, IE 3 and 4
// are used to prove 5.
#[derive(Debug)]
pub struct TraceMgr<T : Tracer> {
    pub tracer : T,
    pub stack : Vec<Step>,
    pub step_idx_counter : usize,
    pub item_storage : ForkStorage,
}


// New needs to be passed an already made ForkStorage::fork(base)
impl<T : Tracer> TraceMgr<T> {
    #[allow(unused_must_use)]
    fn new(base : ForkStorage, mut tracer : T, announcement : Option<String>) -> Self {
        if let Some(s) = announcement {
            tracer.trace_info(s);
        }

        TraceMgr {
            tracer,
            stack : Vec::with_capacity(100),
            step_idx_counter : 0usize,
            item_storage : base,
        }
    }

    pub fn new_arc_trace_mgr(b : &ArcBaseStorage, tracer : T, announcement : Option<String>) -> ArcTraceMgr<T> {
        let fork = ForkStorage::from_arc_base(b);
        let trace_mgr = TraceMgr::new(fork, tracer, announcement);
        Arc::new(RwLock::new(trace_mgr))
    }

    #[allow(unused_must_use)]
    pub fn trace_step(&mut self, s : &Step) {
        self.tracer.trace_step(s);
    }

    pub fn next_step_idx(&mut self) -> StepIdx {
        let this_idx = self.step_idx_counter;
        self.step_idx_counter += 1;
        StepIdx(this_idx)
    }

    pub fn stack_len(&self) -> usize {
        self.stack.len()
    }

    pub fn next_safety_idx(&self) -> SafetyIdx {
        let as_usize = SAFETY_IDX_COUNTER.fetch_add(1, Relaxed);
        SafetyIdx(as_usize)
    }

    pub fn push(&mut self, step : Step) {
        self.stack.push(step);
    }

    /// the `safety_idx` argument automatically gets added
    /// by the `#[trace(..)] macro since it's in reference
    /// to something added by the macro
    pub fn push_extra(&mut self, s : String, safety_idx : SafetyIdx) {
        let this_step : &mut Step = self.stack
                                        .as_mut_slice()
                                        .last_mut()
                                        .expect("Should never be `None` 4");
        assert_eq!(this_step.get_safety_idx(), &safety_idx);
        this_step.get_mut_extras().push(s);
    }

    pub fn pop(&mut self) -> Step {
        self.stack.pop().unwrap()
    }

    // Given some child step/reference's step index,
    // get it's parent by looking on top of the stack, and push 
    // the given step index to the parent's list of referred-to children.
    pub fn add_child(&mut self, child : StepIdx, child_step : &Step) {
        if let Some(step_atop_stack) = self.stack.last_mut() {
            step_atop_stack.get_mut_references().push(child);
        } else {
            // Assert that the current step is the root of the tree
            // by asserting that it's step number is higher than all
            // of the others in the tree.
            let self_idx_usize = (child_step.get_self_idx().as_ref().map(|x| x.to_usize()).expect("A"));
            // FIXME delete this; currently for debugging.
            let self_idx_usize2 = (child_step.get_self_idx().as_ref().map(|x| *x).expect("Should not be none").to_usize());
            assert_eq!(self_idx_usize, self_idx_usize2);
            assert_eq!(self_idx_usize + 1, self.step_idx_counter);
        }
    }
}


/*
I think the idea is that TypeChecker would have a field T,
where that T item would dictate what happens to the elements being
traced.


*/

/*
The contract for the `get_new` method is that it creates whatever you
would consider to be a brand new instance of a particular tracer.
So if your tracer internally uses a BufWriter<File> as its sink, 
get_new() would get another copy of the `File` so it's writing
to the correct sink, and then wrap it in a brand new BufWriter
so the buffers aren't interfering.
This is needed since the library needs to know how to duplicate
your tracer, but there are issues with `clone` when it comes
to file handles/elements implementing `std::io::Write`
*/
pub trait Tracer {
    fn get_new(&self) -> Self;
    // Trace a step
    fn trace_step(&mut self, s : &Step) -> IoResult<usize>;
    // Trace a string (for pseudo-logging)
    fn trace_info(&mut self, s : String) -> IoResult<usize>;
    fn write_to(&mut self, _buf : &[u8]) -> IoResult<usize> {
        Ok(0usize)
    }

    // Trace all of the `TraceItem` elements.
    // This one is a giant pain in the ass and it seems unlikely that you'll
    // want/need to change this one, so it has a default implementation.
    fn trace_items(&mut self, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut bytes_written = 0usize;
        for (idx, item) in storage.to_inner().iter().enumerate() {
            if storage.is_base() {
                bytes_written += self.write_to(format!("{}.", UnivIdx(idx)).as_bytes())?;
            } else {
                bytes_written += self.write_to(format!("{}.", ForkIdx(idx)).as_bytes())?;
            }
            bytes_written += self.trace_items_core(item, storage)?;
            bytes_written += self.write_to(b"\n")?
        }
        // Uncomment if you want large items to be separated
        // by a newline character.
        //bytes_written += self.write_to(b"\n")?;

        Ok(bytes_written)
    }

    fn trace_items_core(&mut self, item : &TraceItem, storage : &impl IsItemStorage) -> IoResult<usize> {
        match item {
            NameItem(ref n) => self.fmt_name_item(n, storage),
            LevelItem(ref l) => self.fmt_level_item(l, storage),
            ExprItem(ref e) => self.fmt_expr_item(e, storage),
            BinderItem(ref b) => self.fmt_binder_item(b, storage),
            VecItem(ref v) => self.fmt_vec_item(v, storage),
            OptionItem(ref o) => self.fmt_option_item(o, storage),
            BoolItem(b) => self.fmt_bool_item(*b, storage),
            UnitItem => self.write_to(b"#UNIT"),
            TupleItem(tup) => self.fmt_tuple_item(tup, storage),
            RecursorRuleItem(inner) => self.fmt_recursor_rule_item(&inner, storage),
            DeltaResultItem(inner) => self.fmt_delta_result_item(&inner, storage),
            ConstantBaseItem(inner) => self.fmt_constant_base_item(&inner, storage),
            ConstantInfoItem(inner) => self.fmt_constant_info_item(&inner, storage),
            ConstructorItem(inner) => self.fmt_constructor_item(&inner, storage),
            InductiveTypeItem(inner) => self.fmt_inductive_type_item(&inner, storage),
            UsizeItem(n) => {
                self.write_to(b"#USIZE")?;
                self.write_to(n.to_string().as_bytes())
            }
        }
    }

    fn fmt_name_item(&mut self, n : &Name, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        match n.as_ref() {
            Anon => wrote += self.write_to(b"#ANON")?,
            Str(pfx, hd) => {
                wrote += self.write_to(b"#NS.")?;
                wrote += self.write_to(storage.get_idx_infallible(pfx).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(hd.to_string().as_bytes())?;
            },
            Num(pfx, hd) => {
                wrote += self.write_to(b"#NI.")?;
                wrote += self.write_to(storage.get_idx_infallible(pfx).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(hd.to_string().as_bytes())?;
            }
       }
       Ok(wrote)

    }

    fn fmt_level_item(&mut self, l : &Level, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        match l.as_ref() {
            Zero => wrote += self.write_to(b"#ZERO")?,
            Succ(inner) => {
                wrote += self.write_to(b"#US.")?;
                wrote += self.write_to(storage.get_idx_infallible(inner).to_string().as_bytes())?;
            },
            Max(lhs, rhs) => {
                wrote += self.write_to(b"#UM.")?;
                wrote += self.write_to(storage.get_idx_infallible(lhs).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(rhs).to_string().as_bytes())?;
            },
            IMax(lhs, rhs) => {
                wrote += self.write_to(b"#UIM.")?;
                wrote += self.write_to(storage.get_idx_infallible(lhs).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(rhs).to_string().as_bytes())?;
            }
            Param(p) => {
                wrote += self.write_to(b"#UP.")?;
                wrote += self.write_to(storage.get_idx_infallible(p).to_string().as_bytes())?;
            }
        }
        Ok(wrote)
    }
    fn fmt_expr_item(&mut self, e : &Expr, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        match e.as_ref() {
            Var { dbj, .. } => {
                wrote += self.write_to(b"#EV.")?;
                wrote += self.write_to(dbj.to_string().as_bytes())?;
            }
            Sort { level, .. } => {
                wrote += self.write_to(b"#ES.")?;
                wrote += self.write_to(storage.get_idx_infallible(level).to_string().as_bytes())?;
            }
            Const { name, levels, .. } => {
                wrote += self.write_to(b"#EC.")?;
                wrote += self.write_to(storage.get_idx_infallible(name).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(levels).to_string().as_bytes())?;
            }
            App { fun, arg, .. } => {
                wrote += self.write_to(b"#EA.")?;
                wrote += self.write_to(storage.get_idx_infallible(fun).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(arg).to_string().as_bytes())?;
            }
            Pi { binder, body, .. } => {
                wrote += self.write_to(b"#EP.")?;
                self.fmt_binder_item(binder, storage)?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(body).to_string().as_bytes())?;
            }
            Lambda { binder, body, .. } => {
                wrote += self.write_to(b"#EL.")?;
                self.fmt_binder_item(binder, storage)?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(body).to_string().as_bytes())?;
            }
            Let { binder, val, body, .. } => {
                wrote += self.write_to(b"#EZ.")?;
                self.fmt_binder_item(binder, storage)?;
                wrote += self.write_to(storage.get_idx_infallible(val).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(body).to_string().as_bytes())?;
            }
            Local { binder, .. } => {
                wrote += self.write_to(b"#EX.")?;
                self.fmt_binder_item(binder, storage)?;
            }
        }
        Ok(wrote)
    }

    fn fmt_binder_item(&mut self, binder : &Binder, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        match &binder.style {
            Default        => wrote += self.write_to(b"#BD.")?,
            Implicit       => wrote += self.write_to(b"#BI.")?,
            StrictImplicit => wrote += self.write_to(b"#BS.")?,
            InstImplicit   => wrote += self.write_to(b"#BC.")?,
        };
        wrote += self.write_to(storage.get_idx_infallible(&binder.pp_name).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&binder.type_).to_string().as_bytes())?;
        Ok(wrote)
    }

    fn fmt_vec_item(&mut self, v : &Vec<ItemIdx>, _ : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#VEC.")?;
        for elem in v.iter() {
            wrote += self.write_to(elem.to_string().as_bytes())?;
        }
        Ok(wrote)
    }
    fn fmt_option_item(&mut self, elem : &Option<ItemIdx>, _ : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        if let Some(idx) = elem {
            wrote += self.write_to(b"#SOME.")?;
            wrote += self.write_to(idx.to_string().as_bytes())?;
        } else {
            wrote += self.write_to(b"#NONE.")?;
        }
 
        Ok(wrote)
    }

    fn fmt_bool_item(&mut self, b : bool, _ : &impl IsItemStorage) -> IoResult<usize> {
        if b {
            self.write_to(b"#TRUE")
        } else {
            self.write_to(b"#FALSE")
        }
    }

    fn fmt_tuple_item(&mut self, pair : &(ItemIdx, ItemIdx), _ : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#TUPLE.")?;
        wrote += self.write_to(pair.0.to_string().as_bytes())?;
        wrote += self.write_to(pair.1.to_string().as_bytes())?;
        Ok(wrote)
    }

    fn fmt_recursor_rule_item(&mut self, rr : &RecursorRule, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#RECURSOR_RULE.")?;
        wrote += self.write_to(storage.get_idx_infallible(&rr.constructor).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&rr.rhs).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        // num_fields
        wrote += self.write_to(rr.nfields.to_string().as_bytes())?;
        Ok(wrote)
    }

    fn fmt_delta_result_item(&mut self, res : &DeltaResult, storage : &impl IsItemStorage) -> IoResult<usize> {
        use DeltaResult::*;
        let mut wrote = 0usize;
        match res {
            Continue(e1, e2) => {
                wrote += self.write_to(b"#CONTINUE.")?;
                wrote += self.write_to(storage.get_idx_infallible(&e1).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(&e2).to_string().as_bytes())?;
            },
            Short(EqShort) => wrote += self.write_to(b"#EQSHORT")?,
            Short(NeqShort) => wrote += self.write_to(b"#NEQSHORT")?,
            Unknown => wrote += self.write_to(b"#UNKNOWN")?,
        }
        Ok(wrote)
    }

    fn fmt_constant_base_item(&mut self, c : &ConstantBase, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#CONSTANT_VAL.")?;
        wrote += self.write_to(storage.get_idx_infallible(&c.name).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&c.lparams).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&c.type_).to_string().as_bytes())?;
        Ok(wrote)
    }

    fn fmt_reducibility_hint(&mut self, hint : &ReducibilityHint, _ : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        match hint {
            ReducibilityHint::Regular(height) => wrote += self.write_to(format!("#REGULAR {}", height).as_bytes())?,
            ReducibilityHint::Opaque => wrote += self.write_to(b"#OPAQUE")?,
            ReducibilityHint::Abbreviation => wrote += self.write_to(b"#ABBREVIATION")?,
        }
        Ok(wrote)

    }

    fn fmt_constant_info_item(&mut self, c : &ConstantInfo, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        let base_idx = storage.get_idx_infallible(c.get_constant_base()).to_string();
        match c {
            AxiomInfo(AxiomVal { is_unsafe, .. }) => {
                wrote += self.write_to(b"#AXIOM_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_unsafe.to_string().as_bytes())?;
            },
            DefinitionInfo(DefinitionVal { value, hint, is_unsafe, .. }) => {
                wrote += self.write_to(b"#DEFINITION_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(value).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.fmt_reducibility_hint(hint, storage)?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_unsafe.to_string().as_bytes())?;
            },
            TheoremInfo(TheoremVal { value, .. }) => {
                wrote += self.write_to(b"#THEOREM_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(value).to_string().as_bytes())?;
            }
            OpaqueInfo(OpaqueVal { value, .. }) => {
                wrote += self.write_to(b"#OPAQUE_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(&value).to_string().as_bytes())?;
            }
            QuotInfo(QuotVal { .. }) => { 
                wrote += self.write_to(base_idx.as_bytes())?;
            },
            InductiveInfo(InductiveVal { all, cnstrs, nparams, nindices, is_rec, is_unsafe, is_reflexive, .. }) => {
                wrote += self.write_to(b"#INDUCTIVE_INFO")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(all).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(cnstrs).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nparams.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nindices.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_rec.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_reflexive.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_unsafe.to_string().as_bytes())?;
           }
            ConstructorInfo(ConstructorVal { induct, cidx, nparams, nfields, is_unsafe, .. }) => {
                wrote += self.write_to(b"#CONSTRUCTOR_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(induct).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(cidx.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nparams.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nfields.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_unsafe.to_string().as_bytes())?;
            }
            RecursorInfo(RecursorVal { all, rules, nparams, nindices, nmotives, nminors, is_k, is_unsafe, .. }) => {
                wrote += self.write_to(b"#RECURSOR_INFO.")?;
                wrote += self.write_to(base_idx.as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(all).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(storage.get_idx_infallible(rules).to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nparams.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nindices.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nmotives.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(nminors.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_k.to_string().as_bytes())?;
                wrote += self.write_to(b".")?;
                wrote += self.write_to(is_unsafe.to_string().as_bytes())?;
           }
        }

        Ok(wrote)

    }

    fn fmt_constructor_item(&mut self, cnstr : &Constructor, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#CONSTRUCTOR.")?;
        wrote += self.write_to(storage.get_idx_infallible(&cnstr.name).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&cnstr.type_).to_string().as_bytes())?;
        Ok(wrote)

    }

    fn fmt_inductive_type_item(&mut self, ind : &InductiveType, storage : &impl IsItemStorage) -> IoResult<usize> {
        let mut wrote = 0usize;
        wrote += self.write_to(b"#INDUCTIVE_TYPE.")?;
        wrote += self.write_to(storage.get_idx_infallible(&ind.name).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&ind.type_).to_string().as_bytes())?;
        wrote += self.write_to(b".")?;
        wrote += self.write_to(storage.get_idx_infallible(&ind.constructors).to_string().as_bytes())?;
        Ok(wrote)
    }

}

impl Tracer for () {
    fn get_new(&self) -> Self { () }
    
    fn trace_step(&mut self, _ : &Step) -> IoResult<usize> { 
        Ok(0) 
    }

    fn trace_info(&mut self, _ : String) -> IoResult<usize> { 
        Ok(0) 
    }
}


// Enum that wraps data that is tracked by the steps being traced
// IE, for a step showing that two expressions `e1` and `e2` are definitionally
// equal, we need to keep know the identities of `e1` and `e2`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TraceItem {
    NameItem(Name),
    LevelItem(Level),
    ExprItem(Expr),
    BinderItem(Binder),
    OptionItem(Option<ItemIdx>),
    BoolItem(bool),
    VecItem(Vec<ItemIdx>),
    TupleItem((ItemIdx, ItemIdx)),
    UnitItem,

    ConstantBaseItem(ConstantBase),
    DeltaResultItem(DeltaResult),
    ConstantInfoItem(ConstantInfo),

    //InductiveDeclarItem(InductiveDeclar),
    InductiveTypeItem(InductiveType),
    ConstructorItem(Constructor),
    RecursorRuleItem(RecursorRule),
    UsizeItem(usize)
}


impl<T : Tracer> std::ops::Drop for TraceMgr<T> {
    #[allow(unused_must_use)]
    fn drop(&mut self) {
        // FIXME Should this be implemented on item storage instead?
        self.tracer.trace_items(&self.item_storage);
   }
}


#[derive(Debug, Clone)]
pub struct BaseStorage {
    items : IndexSet<TraceItem>,
}

impl BaseStorage {
    pub fn new() -> Self {
        BaseStorage {
            items : IndexSet::new()
        }
    }

    pub fn new_arc_base_storage() -> ArcBaseStorage {
        let mut set = IndexSet::new();
        let anon_idx = UnivIdx(set.insert_full(NameItem(mk_anon())).0);
        let zero_idx = UnivIdx(set.insert_full(LevelItem(mk_zero())).0);
        let tt_idx   = UnivIdx(set.insert_full(BoolItem(true)).0);
        let ff_idx   = UnivIdx(set.insert_full(BoolItem(false)).0);
        set.insert(OptionItem(Some(anon_idx)));
        set.insert(OptionItem(Some(zero_idx)));
        set.insert(OptionItem(Some(tt_idx)));
        set.insert(OptionItem(Some(ff_idx)));
        set.insert(OptionItem(None));
        set.insert(UnitItem);
        set.insert(VecItem(Vec::new()));
        assert!(set.len() == 11);
        let univ_items = BaseStorage {
            items : set,
        };
        Arc::new(RwLock::new(univ_items))
    }
}

#[derive(Debug, Clone)]
pub struct ForkStorage {
    base : ArcBaseStorage,
    forked_at : usize,
    items : IndexSet<TraceItem>,
}

impl ForkStorage {
    // Beacuse you want the cloned item to ONLY be of the Arc<...>
    // and not of the underlying collection.
    pub fn from_arc_base(b : &ArcBaseStorage) -> Self {
        ForkStorage {
            base : b.clone(),
            forked_at : b.read().items.len(),
            items : IndexSet::new()
        }
    }
}



pub trait IsItemStorage 
where Self : Sized {
    fn get_idx<A>(&self, item : &A) -> Option<ItemIdx>
        where A : HasUpcastItem + Clone;
    fn insert(&mut self, item : TraceItem) -> ItemIdx;
    fn is_base(&self) -> bool;
    fn to_inner(&self) -> &IndexSet<TraceItem>;


    fn get_idx_infallible<A>(&self, a : &A) -> ItemIdx
    where A : HasUpcastItem + Clone {
        let trace_item = a.upcast_item(self);
        match self.get_idx(&trace_item) {
            Some(idx) => idx,
            None => {
                panic!("This is a fatal error")
            }
        }
    }
}

impl IsItemStorage for BaseStorage {
    fn get_idx<A>(&self, item : &A) -> Option<ItemIdx> 
    where A : HasUpcastItem + Clone {
        let item = item.upcast_item(self);
        self.items
            .get_full(&item)
            .map(|(idx, _)| UnivIdx(idx))
    }

    fn insert(&mut self, item : TraceItem) -> ItemIdx {
        if let Some(idx) = self.get_idx(&item) {
            idx
        } else {
            UnivIdx(self.items.insert_full(item).0)
        }
    }

    fn is_base(&self) -> bool {
        true
    }

    fn to_inner(&self) -> &IndexSet<TraceItem> {
        &self.items
    }

}

impl IsItemStorage for ForkStorage {
    fn get_idx<A>(&self, item : &A) -> Option<ItemIdx> 
    where A : HasUpcastItem + Clone {
        let item = item.upcast_item(self);
        if let Some(u_idx) = self.base.read().get_idx(&item) {
            Some(u_idx)
        } else if let Some((raw_fidx, _)) = self.items.get_full(&item) {
            Some(ForkIdx(raw_fidx))
        } else {
            None
        }
   }

    fn insert(&mut self, item : TraceItem) -> ItemIdx {
        if let Some(idx) = self.base.read().get_idx(&item) {
            idx
        } else {
            ForkIdx(self.items.insert_full(item).0)
        }
    }

    fn is_base(&self) -> bool {
        false
    }

    fn to_inner(&self) -> &IndexSet<TraceItem> {
        &self.items
    }
}

pub trait HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx;
}

impl HasInsertItem for Name {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        if let Some(idx) = storage.get_idx(&self) {
            idx
        } else {
            let _wait_for = match self.as_ref() {
                Anon => panic!("name `Anon` should already exist!"),
                Str(pfx, _) | Num(pfx, _) => pfx.insert_item(storage),
            };

            let as_item = NameItem(self.clone());
            assert!(storage.get_idx(&as_item).is_none());
            storage.insert(as_item)
        }
    }
}

impl HasInsertItem for Level {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {

        if let Some(idx) = storage.get_idx(&self) {
            idx
        } else {
            let _wait_for = match self.as_ref() {
                Zero => panic!("Sort `Zero` should already exist!"),
                Succ(inner) => inner.insert_item(storage),
                Max(lhs, rhs) | IMax(lhs, rhs) => {
                    lhs.insert_item(storage);
                    rhs.insert_item(storage)
                },
                Param(p) => p.insert_item(storage),
            };

            let as_item = LevelItem(self.clone());
            assert!(storage.get_idx(&as_item).is_none());
            storage.insert(as_item)
        }

    }
}

impl HasInsertItem for Binder {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        (&self.pp_name).insert_item(storage);
        (&self.type_).insert_item(storage);
        storage.insert(BinderItem(self))
    }
}

impl HasInsertItem for Expr {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        if let Some(idx) = storage.get_idx(&self) {
            idx
        } else {
            let _wait_for = match self.as_ref() {
                Var {..} => (),
                Sort { level, .. } => { level.insert_item(storage); },
                Const { name, levels, .. } => {
                    name.insert_item(storage);
                    levels.insert_item(storage);
                },
                App { fun, arg, .. } => {
                    fun.insert_item(storage);
                    arg.insert_item(storage);
                },
                Lambda { binder, body, .. } | Pi { binder, body, .. } => {
                    (&binder.pp_name).insert_item(storage);
                    (&binder.type_).insert_item(storage);
                    body.insert_item(storage);
                },
                Let { binder, val, body, .. } => {
                    (&binder.pp_name).insert_item(storage);
                    (&binder.type_).insert_item(storage);
                    val.insert_item(storage);
                    body.insert_item(storage);
                },
                Local { binder, .. } => {
                    (&binder.pp_name).insert_item(storage);
                    (&binder.type_).insert_item(storage);
                }
            };

            let as_item = ExprItem(self.clone());
            assert!(storage.get_idx(&as_item).is_none());
            storage.insert(as_item)
        }
    }
}




impl<A> HasInsertItem for Option<A>
where A : HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            None => storage.insert(OptionItem(None)),
            Some(x) => {
                let inner_idx = x.insert_item(storage);
                storage.insert(OptionItem(Some(inner_idx)))
            }
        }
    }
}

impl HasInsertItem for bool {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            true => storage.insert(BoolItem(true)),
            false => storage.insert(BoolItem(false)),
        }
    }
}

impl HasInsertItem for Cheap {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            CheapTrue => storage.insert(BoolItem(true)),
            CheapFalse => storage.insert(BoolItem(false)),
        }
    }
}

impl HasInsertItem for ShortCircuit {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            EqShort => storage.insert(BoolItem(true)),
            NeqShort => storage.insert(BoolItem(false)),
        }
    }
}

impl<A> HasInsertItem for &A 
where A : HasInsertItem + Clone {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        self.clone().insert_item(storage)
    }
}

impl<A> HasInsertItem for Vec<A>
where A : HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        let mut buf = Vec::with_capacity(self.len());

        for elem in self {
            buf.push(elem.insert_item(storage));
        }

        storage.insert(VecItem(buf))
    }
}

impl<A, B> HasInsertItem for (A, B)
where A : HasInsertItem,
      B : HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        let a_idx = self.0.insert_item(storage);
        let b_idx = self.1.insert_item(storage);
        storage.insert(TupleItem((a_idx, b_idx)))
    }
}

impl <A, B> HasInsertItem for Either<A, B> 
where A : HasInsertItem,
      B : HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            Left(a) => a.insert_item(storage),
            Right(b) => b.insert_item(storage),
        }
    }
}

impl HasInsertItem for crate::utils::Judgment {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            crate::utils::Judgment::OK => storage.insert(BoolItem(true)),
            crate::utils::Judgment::NG => storage.insert(BoolItem(false)),
        }
    }
}

impl HasInsertItem for DeltaResult {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            DeltaResult::Continue(e1, e2) => {
                let _v = vec![e1, e2];
                _v.insert_item(storage)
            },
            DeltaResult::Short(EqShort) => storage.insert(BoolItem(true)),
            DeltaResult::Short(NeqShort) => storage.insert(BoolItem(false)),
            DeltaResult::Unknown => storage.insert(OptionItem(None)),

        }
    }
}
impl HasInsertItem for RecursorRule {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        self.constructor.clone().insert_item(storage);
        self.rhs.clone().insert_item(storage);
        storage.insert(RecursorRuleItem(self))
    }

}

impl HasInsertItem for ConstantBase {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        self.name.clone().insert_item(storage);
        self.lparams.clone().insert_item(storage);
        self.type_.clone().insert_item(storage);
        storage.insert(ConstantBaseItem(self))
    }

}

impl HasInsertItem for () {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        storage.insert(UnitItem)
    }
}

impl<A, E> HasInsertItem for Result<A, E> 
where A : HasInsertItem {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        match self {
            Ok(a) => a.insert_item(storage),
            Err(_) => {
                panic!("HasInsertItem for Result<T, E> does not accept Err(e) variants")
            }
        }
    }
}

impl HasInsertItem for ConstantInfo {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        self.get_constant_base().insert_item(storage);

        match &self {
            AxiomInfo(AxiomVal { .. }) => { },
            DefinitionInfo(DefinitionVal { value, .. }) => {
                value.clone().insert_item(storage);
            },
            TheoremInfo(TheoremVal { value, .. }) => {
                value.clone().insert_item(storage);
            }
            OpaqueInfo(OpaqueVal { value, .. }) => {
                value.clone().insert_item(storage);
            }
            QuotInfo(QuotVal { .. }) => { },
            InductiveInfo(InductiveVal { all, cnstrs, .. }) => {
                all.clone().insert_item(storage);
                cnstrs.clone().insert_item(storage);
            }
            ConstructorInfo(ConstructorVal { induct, .. }) => {
                induct.clone().insert_item(storage);
            }
            RecursorInfo(RecursorVal { all, rules, .. }) => {
                all.clone().insert_item(storage);
                rules.clone().insert_item(storage);
            }
        }
            storage.insert(ConstantInfoItem(self))
    }
}

impl HasInsertItem for Constructor {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        (&self.name).insert_item(storage);
        (&self.type_).insert_item(storage);
        storage.insert(ConstructorItem(self))
    }
}

impl HasInsertItem for InductiveType {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        (&self.name).insert_item(storage);
        (&self.type_).insert_item(storage);
        (&self.constructors).insert_item(storage);
        storage.insert(InductiveTypeItem(self))
    }
}

//impl HasInsertItem for InductiveDeclar {
//    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
//        (&self.name).insert_item(storage);
//        (&self.lparams).insert_item(storage);
//        (&self.types).insert_item(storage);
//        storage.get_idx_or_insert(InductiveDeclarItem(self))
//    }
//}

impl HasInsertItem for usize {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        storage.insert(UsizeItem(self))
    }
}

impl HasInsertItem for RecursorVal {
    fn insert_item(self, storage : &mut impl IsItemStorage) -> ItemIdx {
        let as_constant_info = ConstantInfo::RecursorInfo(self);
        as_constant_info.insert_item(storage)
    }
}


pub trait HasUpcastItem {
    fn upcast_item(self, storage : &impl IsItemStorage) -> TraceItem;
}

impl HasUpcastItem for Name {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        NameItem(self)
    }
}
impl HasUpcastItem for Level {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        LevelItem(self)
    }
}

impl HasUpcastItem for Expr {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        ExprItem(self)
    }
}
impl HasUpcastItem for RecursorRule {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        RecursorRuleItem(self)
    }
}
//
impl HasUpcastItem for InductiveType {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        InductiveTypeItem(self)
    }
}
//
impl HasUpcastItem for Constructor {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        ConstructorItem(self)
    }
}

impl HasUpcastItem for ConstantBase {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        ConstantBaseItem(self)
    }
}

impl<T> HasUpcastItem for Vec<T> 
where T : HasUpcastItem {
    fn upcast_item(self, storage : &impl IsItemStorage) -> TraceItem {
        let mut _v = Vec::with_capacity(self.len());
        for elem in self.into_iter().map(|x| x.upcast_item(storage)) {
            _v.push(storage.get_idx_infallible(&elem));
        }

        VecItem(_v)
    }
}

impl HasUpcastItem for TraceItem {
    fn upcast_item(self, _ : &impl IsItemStorage) -> TraceItem {
        self
    }
}

impl<A> HasUpcastItem for &A 
where A : HasUpcastItem + Clone {
    fn upcast_item(self, storage : &impl IsItemStorage) -> TraceItem {
        self.clone().upcast_item(storage)
    }
}
