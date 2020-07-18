
use std::io::Write;
use nanoda_macros::is_step;
use crate::utils::{ Ptr, ListPtr, IsCtx };
use crate::name::{ NamePtr, NamesPtr, StringPtr };
use crate::level::{ LevelPtr, LevelsPtr };
use crate::expr::{ ExprPtr, ExprsPtr, BinderStyle, LocalSerial };
use crate::inductive::{ IndBlockPtr, CheckedIndBlockPtr };
use crate::tc::infer::InferFlag;
use crate::tc::eq::{ EqResult, DeltaResult }; 
use crate::trace::IsTracer;
use crate::trace::items::HasPrefix;
use crate::env::{ 
    DeclarView,
    RecRulePtr, 
    RecRulesPtr, 
    DeclarPtr, 
    DeclarsPtr, 
    ReducibilityHint 
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StepIdx(pub usize);

impl StepIdx {
    pub fn new(n : usize) -> Self {
        StepIdx(n)
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Step<H> {
    Live {
        // The index of this (from the caller's perspective, the child)
        // step in the trace output, and a phantom type saying
        // what the evidence is proof of (IE `WhnfCore`)
        //evidence : Evidence<H>,
        step_idx : StepIdx,
        evidence : H,
    },
    Pfind {
        evidence : H,
    },
    Noop {
        evidence : H,
    },
}

impl<H : Default + std::fmt::Debug> Step<H> {
    pub fn new_pfind<'a, CTX : IsCtx<'a>>(_ : &CTX) -> Self {
        assert!(<CTX as IsCtx>::IS_PFINDER);
        Step::Pfind { 
            evidence : Default::default()
        }
    }

    pub fn new_noop<'a, CTX : IsCtx<'a>>(_ : &CTX) -> Self {
        assert!(<CTX as IsCtx>::Tracer::NOOP);
        Step::Noop {
            evidence : Default::default()
        }
    }

    pub fn new_live<'a, CTX : IsCtx<'a>>(step_idx : StepIdx, _ : &CTX) -> Self {
        assert!(!<CTX as IsCtx>::IS_PFINDER);
        Step::Live {
            step_idx,
            evidence : Default::default()
        }
    }

}


#[is_step(tag = "LP", result_type = "Option<usize>", fun = "trace_pos")]
#[derive(Debug, Clone, Copy)]
pub enum Pos<'a, A : HasPrefix> {
    #[N]
    BaseNone {
        needle : Ptr<'a, A>,
        haystack : ListPtr<'a, A>,
        #[result]
        pos : Option<usize>,
    },
    #[O]
    BaseSome {
        needle : Ptr<'a, A>,
        haystack_tl : ListPtr<'a, A>,
        haystack : ListPtr<'a, A>,
        #[result]
        pos : Option<usize>,
    },
    #[S]
    Step {
        needle : Ptr<'a, A>,
        x : Ptr<'a, A>,
        haystack_tl : ListPtr<'a, A>,
        pos : Option<usize>,
        haystack : ListPtr<'a, A>,
        #[result]
        pos_prime  : Option<usize>,
        h1 : Step<PosZst>,
    }
}

#[is_step(tag = "SS", result_type = "bool", fun = "trace_is_subset")]
#[derive(Debug, Clone, Copy)]
pub enum IsSubset<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        super_ : ListPtr<'a, A>,
        sub : ListPtr<'a, A>,
        #[result]
        result : bool,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        maybe_pos : Option<usize>,
        sub : ListPtr<'a, A>,
        super_ : ListPtr<'a, A>,
        result : bool,
        sub_prime : ListPtr<'a, A>,
        #[result]
        result_prime : bool,
        h1 : Step<PosZst>,
        h2 : Step<IsSubsetZst>,
    }
}

#[is_step(tag = "ND", result_type = "bool", fun = "trace_no_dupes")]
#[derive(Debug, Clone, Copy)]
pub enum NoDupes<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        l : ListPtr<'a, A>,
        #[result]
        result : bool,
    },
    #[S]
    StepTt {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        l : ListPtr<'a, A>,
        h1 : Step<PosZst>,
        h2 : Step<NoDupesZst>,
        #[result]
        result : bool,
    }
}


#[is_step(tag = "GP", result_type = "NamePtr<'a>", fun = "trace_get_prefix")]
#[derive(Debug, Clone, Copy)]
pub enum GetPrefix<'a> {
    #[A]
    BaseAnon {
        n : NamePtr<'a>,
        #[result]
        pfx : NamePtr<'a>,
    },
    #[S]
    StepStr {
        #[result]
        pfx : NamePtr<'a>,
        sfx : StringPtr<'a>,
        n : NamePtr<'a>,
    },
    #[N]
    StepNum {
        #[result]
        pfx : NamePtr<'a>,
        sfx : u64,
        n : NamePtr<'a>,
    }
}

#[is_step(tag = "IP", result_type = "bool", fun = "trace_is_param")]
#[derive(Debug, Clone, Copy)]
pub enum IsParam<'a> {
    #[Z]
    Zero {
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[S]
    Succ {
        l : LevelPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[M]
    Max {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : bool

    },
    #[I]
    Imax {
        
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : bool

    },
    #[P]
    Param {
        n : NamePtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : bool
    }    
}

#[is_step(tag = "ZL", result_type = "bool", fun = "trace_is_zero_lit")]
#[derive(Debug, Clone, Copy)]
pub enum IsZeroLit<'a> {
    #[Z]
    Zero {
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[I]
    Imax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[P]
    Param {
        n : NamePtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    }
}

#[is_step(tag = "NS", result_type = "bool", fun = "trace_is_succ")]
#[derive(Debug, Clone, Copy)]
pub enum IsSucc<'a> {
    #[Z]
    Zero {
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool

    },
    #[I]
    Imax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[P]
    Param {
        n : NamePtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    }
}

#[is_step(tag = "AM", result_type = "bool", fun = "trace_is_any_max")]
#[derive(Debug, Clone, Copy)]
pub enum IsAnyMax<'a> {
    #[Z]
    Zero {
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[I]
    Imax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[P]
    Param {
        n : NamePtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool
    }
}

#[is_step(tag = "CO", result_type = "LevelPtr<'a>", fun = "trace_combining")]
#[derive(Debug, Clone, Copy)]
pub enum Combining<'a> {
    #[L]
    Lzero {
        r : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
    },
    
    #[R]
    Rzero {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
    },
    #[S]
    Succ {
        l_pred : LevelPtr<'a>,
        r_pred : LevelPtr<'a>,
        result_prime : LevelPtr<'a>,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        h1 : Step<CombiningZst>,
    },
    #[O]
    Owise {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        h1 : Step<IsZeroLitZst>,
        h2 : Step<IsZeroLitZst>,
        h3 : Step<IsSuccZst>,
        h4 : Step<IsSuccZst>,
    }
}

#[is_step(tag = "SI", result_type = "LevelPtr<'a>", fun = "trace_simplify")]
#[derive(Debug, Clone, Copy)]
pub enum Simplify<'a> {
    #[Z]
    Zero {
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
    },
    #[P]
    Param {
        n : NamePtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        pred_prime : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        fst_prime : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        l : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<SimplifyZst>,
        h3 : Step<CombiningZst>,
    },
    #[IZ]
    ImaxZero {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
    },
    #[IS]
    ImaxSucc {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        fst_prime : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        l : LevelPtr<'a>,
        succ_snd_prime : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<SimplifyZst>,
        h3 : Step<CombiningZst>,
    },
    #[IO]
    ImaxOwise {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        fst_prime : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<IsZeroLitZst>,
        h3 : Step<IsSuccZst>,
        h4 : Step<SimplifyZst>,
    }
}


#[is_step(tag = "PD", result_type = "bool", fun = "trace_params_defined")]
#[derive(Debug, Clone, Copy)]
pub enum ParamsDefined<'a> {
    #[Z]
    Zero {
        params : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<ParamsDefinedZst>,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<ParamsDefinedZst>,
        h2 : Step<ParamsDefinedZst>,
    },
    #[I]
    Imax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<ParamsDefinedZst>,
        h2 : Step<ParamsDefinedZst>,
    },
    #[Q]
    BaseParam {
        n : NamePtr<'a>,
        tl : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        #[result]
        result : bool,

    },
    #[R]
    StepParam {
        n : NamePtr<'a>,
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<ParamsDefinedZst>,
    }
}

#[is_step(tag = "SL", result_type = "LevelPtr<'a>", fun = "trace_subst_l")]
#[derive(Debug, Clone, Copy)]
pub enum SubstL<'a> {
    #[Z]
    Zero {
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        #[result]
        l : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        pred_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        l_prime : LevelPtr<'a>,
        h1 : Step<SubstLZst>,
    },
    #[M]
    Max {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        fst_prime : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        l_prime : LevelPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
    },
    #[I]
    Imax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        fst_prime : LevelPtr<'a>,
        snd_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        l_prime : LevelPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
    },
    #[N]
    ParamNil {
        n : NamePtr<'a>,
        #[result]
        l : LevelPtr<'a>,
        nil : LevelsPtr<'a>,
    },
    #[H]
    ParamHit {
        n : NamePtr<'a>,
        #[result]
        v : LevelPtr<'a>,
        ks_tl : LevelsPtr<'a>,
        vs_tl : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
    },
    #[M]
    ParamMiss {
        n : NamePtr<'a>,
        k : LevelPtr<'a>,
        v : LevelPtr<'a>,
        #[result]
        l_prime : LevelPtr<'a>,
        ks_tl : LevelsPtr<'a>,
        vs_tl : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
    }
}

#[is_step(tag = "PS", result_type = "bool", fun = "trace_params_defined_many")]
#[derive(Debug, Clone, Copy)]
pub enum ParamsDefinedMany<'a> {
    #[B]
    Base {
        params : LevelsPtr<'a>,
        ls : LevelsPtr<'a>,
        #[result]
        result  : bool,
    },
    #[S]
    Step {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        params  : LevelsPtr<'a>,
        ls : LevelsPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<ParamsDefinedManyZst>,
        h2 : Step<ParamsDefinedZst>,
    }
}


#[is_step(tag = "SM", result_type = "LevelsPtr<'a>", fun = "trace_subst_l_many")]
#[derive(Debug, Clone, Copy)]
pub enum SubstLMany<'a> {
    #[B]
    Base {
        ls : LevelsPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        #[result]
        ls_prime : LevelsPtr<'a>,
    },
    #[S]
    Step {
        ls_hd : LevelPtr<'a>,
        ls_hd_prime : LevelPtr<'a>,
        ls_tl : LevelsPtr<'a>,
        ls_tl_prime : LevelsPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        ls : LevelsPtr<'a>,
        #[result]
        ls_prime : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLManyZst>,
    }
}

#[is_step(tag = "FI", result_type = "LevelPtr<'a>", fun = "trace_fold_imaxs")]
#[derive(Debug, Clone, Copy)]
pub enum FoldImaxs<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        ls : LevelsPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
    },
    #[S]
    Step {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : LevelPtr<'a>,
        ls : LevelsPtr<'a>,
        combined : LevelPtr<'a>,
        h1 : Step<FoldImaxsZst>,
    }
}

#[is_step(tag = "EIL", result_type = "bool", fun = "trace_ensure_imax_leq")]
#[derive(Debug, Clone, Copy)]
pub enum EnsureImaxLeq<'a> {
    #[B]
    Base {
        i_snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        l_z : LevelPtr<'a>,
        r_z : LevelPtr<'a>,
        l_z_prime : LevelPtr<'a>,
        r_z_prime : LevelPtr<'a>,
        l_s : LevelPtr<'a>,
        r_s : LevelPtr<'a>,
        l_s_prime : LevelPtr<'a>,
        r_s_prime : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        pp : LevelsPtr<'a>,
        zz : LevelsPtr<'a>,
        s_pp : LevelsPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
        h3 : Step<SimplifyZst>,
        h4 : Step<SimplifyZst>,
        h5 : Step<LeqCoreZst>,
        h6 : Step<SubstLZst>,
        h7 : Step<SubstLZst>,
        h8 : Step<SimplifyZst>,
        h9 : Step<SimplifyZst>,
        h10 : Step<LeqCoreZst>,
    }

}

#[is_step(tag = "QC", result_type = "bool", fun = "trace_leq_core")]
#[derive(Debug, Clone, Copy)]
pub enum LeqCore<'a> {
    #[ZA]
    ZAny {
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[AZ]
    AnyZ {
        l : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        r : LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[PP]
    ParamParam {
        n1 : NamePtr<'a>,
        n2 : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[PZ]
    ParamZero {
        n : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r: LevelPtr<'a>,
        #[result]
        result : bool,
    },
    #[ZP]
    ZeroParam {
        n : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : bool,

    },
    #[SA]
    SuccAny {
        l_pred : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        l_h_prime : usize,
        l : LevelPtr<'a>,
        h1 : Step<LeqCoreZst>,
    },
    #[AS]
    AnySucc {
        l : LevelPtr<'a>,
        r_pred : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        r_h_prime : usize,
        r : LevelPtr<'a>,
        h1 : Step<LeqCoreZst>,
    },
    #[MA]
    MaxAny {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        b1 : bool,
        b2 : bool,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
    },
    #[PM]
    ParamMax {
        n : NamePtr<'a>,
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
    },
    #[ZM]
    ZeroMax {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
    },
    #[IC]
    ImaxCongr {
        fst : LevelPtr<'a>,
        snd : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        result : bool
    },
    #[IL]
    ImaxParamL {
        n : NamePtr<'a>,
        fst : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        snd : LevelPtr<'a>,
        l : LevelPtr<'a>,
        h1 : Step<EnsureImaxLeqZst>,
    },
    #[IR]
    ImaxParamR {
        n : NamePtr<'a>,
        fst : LevelPtr<'a>,
        l : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        snd : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<EnsureImaxLeqZst>,
    },
    #[LI] 
    ImaxImaxAny {
        a : LevelPtr<'a>,
        c : LevelPtr<'a>,
        d : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        l_prime: LevelPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<LeqCoreZst>,
    },
    #[LM] 
    ImaxMaxAny {
        a : LevelPtr<'a>,
        c : LevelPtr<'a>,
        d : LevelPtr<'a>,
        r : LevelPtr<'a>,
        new_max_prime : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        l_prime : LevelPtr<'a>,
        l : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<LeqCoreZst>,
    },
    #[RI]
    AnyImaxImax {
        l : LevelPtr<'a>,
        x : LevelPtr<'a>,
        j : LevelPtr<'a>,
        k : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        r_prime : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<LeqCoreZst>,
    },
    #[RM]
    AnyImaxMax {
        l : LevelPtr<'a>,
        x : LevelPtr<'a>,
        j : LevelPtr<'a>,
        k : LevelPtr<'a>,
        new_max_prime : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        result : bool,
        r_prime : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<LeqCoreZst>,
    }
}

#[is_step(tag = "LE", result_type = "bool", fun = "trace_leq")]
#[derive(Debug, Clone, Copy)]
pub enum Leq<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<SimplifyZst>,
        h2 : Step<SimplifyZst>,
        h3 : Step<LeqCoreZst>,
    }
}

#[is_step(tag = "LQ", result_type = "bool", fun = "trace_eq_antisymm")]
#[derive(Debug, Clone, Copy)]
pub enum EqAntisymm<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        #[result]
        result : bool,
        h1 : Step<LeqZst>,
        h2 : Step<LeqZst>,
    }
}

#[is_step(tag = "IZ", result_type = "bool", fun = "trace_is_zero")]
#[derive(Debug, Clone, Copy)]
pub enum IsZero<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<LeqZst>,
    }
}


#[is_step(tag = "NZ", result_type = "bool", fun = "trace_is_nonzero")]
#[derive(Debug, Clone, Copy)]
pub enum IsNonzero<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<LeqZst>,
    }
}

#[is_step(tag = "MZ", result_type = "bool", fun = "trace_maybe_zero")]
#[derive(Debug, Clone, Copy)]
pub enum MaybeZero<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<IsNonzeroZst>,
    }
}

#[is_step(tag = "MN", result_type = "bool", fun = "trace_maybe_nonzero")]
#[derive(Debug, Clone, Copy)]
pub enum MaybeNonzero<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<IsZeroZst>,
    }
}

#[is_step(tag = "EM", result_type = "bool", fun = "trace_eq_antisymm_many")]
#[derive(Debug, Clone, Copy)]
pub enum EqAntisymmMany<'a> {
    #[T]
    Base {
        ls : LevelsPtr<'a>,
        rs : LevelsPtr<'a>,
        #[result]
        result : bool,
    },
    #[L]
    BaseFL {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        ls : LevelsPtr<'a>,
        rs : LevelsPtr<'a>,
        #[result]
        result : bool
    },
    #[R]
    BaseFR {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        ls : LevelsPtr<'a>,
        rs : LevelsPtr<'a>,
        #[result]
        result : bool
    },
    #[S]
    Step {
        l_hd : LevelPtr<'a>,
        r_hd : LevelPtr<'a>,
        l_tl : LevelsPtr<'a>,
        r_tl : LevelsPtr<'a>,
        b1 : bool,
        b2 : bool,
        ls : LevelsPtr<'a>,
        rs : LevelsPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<EqAntisymmZst>,
        h2 : Step<EqAntisymmManyZst>,
    }
}

#[is_step(tag = "I", result_type = "ExprPtr<'a>", fun = "trace_inst")]
#[derive(Debug, Clone, Copy)]
pub enum Inst<'a> {
    #[N]
    NoBound {
        #[result]
        e : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        h1 : bool,
    },
    #[A]
    ByAux {
        e : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
    }
}

#[is_step(tag = "IA", result_type = "ExprPtr<'a>", fun = "trace_inst_aux")]
#[derive(Debug, Clone, Copy)]
pub enum InstAux<'a> {
    #[N]
    NoBound {
        #[result]
        e : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
    },
    #[V]
    VarHit {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
    },
    #[M]
    VarMiss {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_style : BinderStyle,
        b_type : ExprPtr<'a>,
        body : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
    },    
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_style : BinderStyle,
        b_type : ExprPtr<'a>,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        b_type_prime : ExprPtr<'a>,
        val_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
        h3 : Step<InstAuxZst>,
    }      

}

#[is_step(tag="AB", result_type = "ExprPtr<'a>", fun = "trace_abstr")]
#[derive(Debug, Clone, Copy)]
pub enum Abstr<'a> {
    #[N]
    NoLocals {
        #[result]
        e : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
    },
    #[A]
    ByAux {
        e : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
    }

}

#[is_step(tag="AA", result_type = "ExprPtr<'a>", fun = "trace_abstr_aux")]
#[derive(Debug, Clone,  Copy)]
pub enum AbstrAux<'a> {
    #[N]
    NoLocals {
        #[result]
        e : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        offset : u16,
        h1 : bool,
    },
    #[X]
    LocalHit {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        locals : ExprsPtr<'a>,
        offset : u16,
        pos : usize,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<PosZst>,
    },
    #[M]
    LocalMiss {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        locals : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e : ExprPtr<'a>,
        h1 : Step<PosZst>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        offset : u16,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
    },    
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        val_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
        h3 : Step<AbstrAuxZst>,
    }    
}

#[is_step(tag="SE", result_type = "ExprPtr<'a>", fun = "trace_subst_e")]
#[derive(Debug, Clone,  Copy)]
pub enum SubstE<'a> {
    #[V]
    Var {
        dbj : u16,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        #[result]
        e : ExprPtr<'a>,
    },
    #[S]
    Sort {
        l : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        l_prime : LevelPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstLZst>,
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        levels_prime : LevelsPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstLManyZst>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
    },    
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        val_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
        h3 : Step<SubstEZst>,
    },        
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        serial_prime : LocalSerial,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
    },        
}

#[is_step(tag="CH", result_type = "u16", fun = "trace_calc_height_aux")]
#[derive(Debug, Clone,  Copy)]
pub enum CalcHeightAux<'a> {
    #[V]
    Var {
        dbj : u16,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
    },
    #[H]
    ConstHit {
        n : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_val : ExprPtr<'a>,
        #[result]
        height : u16,
        d_is_unsafe : bool,
        e : ExprPtr<'a>,
        d_hint : ReducibilityHint,
        defn : DeclarPtr<'a>,
        h1 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarPtr<'a>),

    },
    #[M]
    ConstMiss {
        n : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
    },
    #[P]
    Pi {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle, 
        b : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
    },
    #[L]
    Lambda {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle, 
        b : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
    },
    #[Z]
    Let {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle, 
        v : ExprPtr<'a>,
        b : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        height3 : u16,
        e : ExprPtr<'a>,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
        h3 : Step<CalcHeightAuxZst>,
    },
}


#[is_step(tag="IO", result_type = "bool", fun = "trace_has_ind_occ")]
#[derive(Debug, Clone,  Copy)]
pub enum HasIndOcc<'a> {
    #[V]
    Var {
        dbj : u16,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        ind_names : NamesPtr<'a>,
    },
    #[S]
    Sort {
        l : LevelPtr<'a>,
        ind_names : NamesPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_names : NamesPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<PosZst>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_names : NamesPtr<'a>,
        b1 : bool,
        b2 : bool,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b1 : bool,
        b2 : bool,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b1 : bool,
        b2 : bool,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
    },
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        b1 : bool,
        b2 : bool,
        b3 : bool,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
        h3 : Step<HasIndOccZst>,
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        e : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<HasIndOccZst>,
    }

}

#[is_step(tag="AP", result_type = "ExprPtr<'a>", fun = "trace_apply_pi")]
#[derive(Debug, Clone,  Copy)]
pub enum ApplyPi<'a> {
    #[B]
    Base {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        body : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        local_dom : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<AbstrZst>,
    }
}

#[is_step(tag="AL", result_type = "ExprPtr<'a>", fun = "trace_apply_lambda")]
#[derive(Debug, Clone,  Copy)]
pub enum ApplyLambda<'a> {
    #[B]
    Base {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        body : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        local_dom : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<AbstrZst>,
    }
}

#[is_step(tag="FP", result_type = "ExprPtr<'a>", fun = "trace_fold_pis")]
#[derive(Debug, Clone,  Copy)]
pub enum FoldPis<'a> {
    #[N]
    Nil {
        #[result]
        body : ExprPtr<'a>,
        binders : ExprsPtr<'a>,
    },
    #[C]
    Cons {
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        body : ExprPtr<'a>,
        sink : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        binders : ExprsPtr<'a>,
        h1 : Step<FoldPisZst>,
        h2 : Step<ApplyPiZst>,
    }
}

#[is_step(tag="FL", result_type = "ExprPtr<'a>", fun = "trace_fold_lambdas")]
#[derive(Debug, Clone,  Copy)]
pub enum FoldLambdas<'a> {
    #[N]
    Nil {
        #[result]
        body : ExprPtr<'a>,
        binders : ExprsPtr<'a>,
    },
    #[C]
    Cons {
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        body : ExprPtr<'a>,
        sink : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        binders : ExprsPtr<'a>,
        h1 : Step<FoldLambdasZst>,
        h2 : Step<ApplyLambdaZst>,
    }
}

#[is_step(tag="FA", result_type = "ExprPtr<'a>", fun = "trace_foldl_apps")]
#[derive(Debug, Clone, Copy)]
pub enum FoldlApps<'a> {
    #[N]
    Nil {
        #[result]
        base : ExprPtr<'a>,
        args : ExprsPtr<'a>,
    },
    #[C]
    Cons {
        base : ExprPtr<'a>,
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        #[result]
        folded : ExprPtr<'a>,
        app : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        h1 : Step<FoldlAppsZst>,
    }
}

#[is_step(tag="UX", result_type = "(ExprPtr<'a>, ExprsPtr<'a>)", fun = "trace_unfold_apps_aux")]
#[derive(Debug, Clone, Copy)]
pub enum UnfoldAppsAux<'a> {
    #[O]
    Base {
        f : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        result : (ExprPtr<'a>, ExprsPtr<'a>),
        h1 : Step<IsAppZst>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        result : (ExprPtr<'a>, ExprsPtr<'a>),
        args_prime : ExprsPtr<'a>,
        e : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
    },
}


#[is_step(tag="TZ", result_type = "u16", fun = "trace_telescope_size")]
#[derive(Debug, Clone, Copy)]
pub enum TelescopeSize<'a> {
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        size : u16,
        h1 : Step<TelescopeSizeZst>,
    },
    #[O]
    Owise {
        e : ExprPtr<'a>,
        #[result]
        size : u16,
        h1 : Step<IsPiZst>,
    }
}


#[is_step(tag="ISA", result_type = "bool", fun = "trace_is_app")]
#[derive(Debug, Clone, Copy)]
pub enum IsApp<'a> {
    #[V]
    Var {
        dbj : u16,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },

}

#[is_step(tag="ISP", result_type = "bool", fun = "trace_is_pi")]
#[derive(Debug, Clone, Copy)]
pub enum IsPi<'a> {
    #[V]
    Var {
        dbj : u16,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },

}

#[is_step(tag="ISC", result_type = "bool", fun = "trace_is_const")]
#[derive(Debug, Clone, Copy)]
pub enum IsConst<'a> {
    #[V]
    Var {
        dbj : u16,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },

}


#[is_step(tag="ISL", result_type = "bool", fun = "trace_is_lambda")]
#[derive(Debug, Clone, Copy)]
pub enum IsLambda<'a> {
    #[V]
    Var {
        dbj : u16,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[Z]
    Let {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : bool,
    },

}



#[is_step(tag="WS", result_type = "ExprPtr<'a>", fun = "trace_whnf_sort")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfSort<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        s : ExprPtr<'a>,
        #[result]
        s_prime : ExprPtr<'a>,
        h1 : Step<SimplifyZst>,
    }
}
#[is_step(tag="WL", result_type = "ExprPtr<'a>", fun = "trace_whnf_lambda")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfLambda<'a> {
    #[X]
    NotLambda {
        eA : ExprPtr<'a>,
        rem_args : ExprsPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        eB : ExprPtr<'a>,
        eC : ExprPtr<'a>,
        #[result]
        eD : ExprPtr<'a>,
        h1 : Step<IsLambdaZst>,
        h2 : Step<InstZst>,
        h3 : Step<FoldlAppsZst>,
        h4 : Step<WhnfCoreZst>,

    },
    #[N]
    NoArgs {
        e_A : ExprPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        e_B : ExprPtr<'a>,
        #[result]
        e_C : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<WhnfCoreZst>,
    },
    #[S]
    Step {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        arg_hd : ExprPtr<'a>,
        args_tl : ExprsPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        #[result]
        b_prime : ExprPtr<'a>,
        lambda : ExprPtr<'a>,
        lambda_args_prime : ExprsPtr<'a>,
        all_args : ExprsPtr<'a>,
        h1 : Step<WhnfLambdaZst>,
    }

}

#[is_step(tag="WZ", result_type = "ExprPtr<'a>", fun = "trace_whnf_let")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfLet<'a> {
    #[B]
    Base {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        v : ExprPtr<'a>,
        bodyA : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        bodyB : ExprPtr<'a>,
        bodyC : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        e : ExprPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<FoldlAppsZst>,
        h3 : Step<WhnfCoreZst>,
    }
}


#[is_step(tag="QL", result_type = "ExprPtr<'a>", fun = "trace_reduce_quot_lift")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceQuotLift<'a> {
    #[B]
    Base {
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        qmk_A_r : ExprPtr<'a>,
        a : ExprPtr<'a>,
        qmk_levels : LevelsPtr<'a>,
        qmk_args : ExprsPtr<'a>,
        out_unred : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        skipped : ExprsPtr<'a>,
        qmk_const : ExprPtr<'a>,
        qlift_const : ExprPtr<'a>,
        qmk_A_r_a_unred : ExprPtr<'a>,
        qmk_A_r_a : ExprPtr<'a>,
        f : ExprPtr<'a>,
        B : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<UnfoldAppsAuxZst>,
        h3 : Step<FoldlAppsZst>,
        h4 : Step<WhnfCoreZst>,
    }
}

#[is_step(tag="QI", result_type = "ExprPtr<'a>", fun = "trace_reduce_quot_ind")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceQuotInd<'a> {
    #[B]
    Base {
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        qmk_A_r : ExprPtr<'a>,
        a : ExprPtr<'a>,
        qmk_levels : LevelsPtr<'a>,
        qmk_args : ExprsPtr<'a>,
        out_unred : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        skipped : ExprsPtr<'a>,
        qmk_const : ExprPtr<'a>,
        qind_const : ExprPtr<'a>,
        B_of : ExprPtr<'a>,
        qmk_A_r_a_unred : ExprPtr<'a>,
        qmk_A_r_a : ExprPtr<'a>,
        B_app : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<UnfoldAppsAuxZst>,
        h3 : Step<FoldlAppsZst>,
        h4 : Step<WhnfCoreZst>,
    }
}


#[is_step(tag="NC", result_type = "ExprPtr<'a>", fun = "trace_mk_nullary_ctor")]
#[derive(Debug, Clone, Copy)]
pub enum MkNullaryCtor<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_num_params : u16,
        d_all_ind_names : NamesPtr<'a>,
        d_all_ctor_names : NamesPtr<'a>,
        d_is_unsafe : bool,
        zth_ctor_name : NamePtr<'a>,
        fold_args : ExprsPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        base : ExprPtr<'a>,
        ind : DeclarPtr<'a>,
        fold_const : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarPtr<'a>),
        h3 : Step<FoldlAppsZst>,
    }
}

#[is_step(tag="WK", result_type = "ExprPtr<'a>", fun = "trace_to_ctor_when_k")]
#[derive(Debug, Clone, Copy)]
pub enum ToCtorWhenK<'a> {
    #[S]
    Skip {
        #[result]
        e : ExprPtr<'a>,
        d : DeclarPtr<'a>,
    },
    #[B]
    Base {
        e : ExprPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_all_names : NamesPtr<'a>,
        d_num_params : u16,
        d_num_indices : u16,
        d_num_motives : u16,
        d_num_minors : u16,
        d_major_idx : u16,
        d_rec_rules : RecRulesPtr<'a>,
        d_is_k : bool,
        d_is_unsafe : bool,
        e_type_unred : ExprPtr<'a>,
        e_type : ExprPtr<'a>,
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        c_args : ExprsPtr<'a>,
        #[result]
        ctor_app : ExprPtr<'a>,
        ctor_app_type : ExprPtr<'a>,
        const_ : ExprPtr<'a>,
        h1 : Step<InferZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<UnfoldAppsAuxZst>,
        h4 : Step<MkNullaryCtorZst>,
        h5 : Step<InferZst>,
        h6 : Step<DefEqZst>,
    },
}


#[is_step(tag="RR", result_type = "RecRulePtr<'a>", fun = "trace_get_rec_rule")]
#[derive(Debug, Clone, Copy)]
pub enum GetRecRule<'a> {
    #[B]
    Base {
        major_name : NamePtr<'a>,
        num_fields : u16,
        val : ExprPtr<'a>,
        rrs_tl : RecRulesPtr<'a>,
        #[result]
        rec_rule : RecRulePtr<'a>,
        rrs : RecRulesPtr<'a>,
    },
    #[S]
    Step {
        ctor_name : NamePtr<'a>,
        num_fields : u16,
        val : ExprPtr<'a>,
        rrs_tl : RecRulesPtr<'a>,
        major_name : NamePtr<'a>,
        #[result]
        out : RecRulePtr<'a>,
        x : RecRulePtr<'a>,
        rec_rules : RecRulesPtr<'a>,
        h1 : Step<GetRecRuleZst>,
    }
}


#[is_step(tag="RI", result_type = "ExprPtr<'a>", fun = "trace_reduce_ind_rec")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceIndRec<'a> {
    #[B]
    Base {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        // rec info
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        all_names : NamesPtr<'a>,
        num_params : u16,
        num_indices : u16,
        num_motives : u16,
        num_minors : u16,
        major_idx : u16,
        rec_rules : RecRulesPtr<'a>,
        is_k : bool,
        is_unsafe : bool,        
        //
        major_unredB : ExprPtr<'a>,
        major_name : NamePtr<'a>,
        major_levels : LevelsPtr<'a>,
        major_args : ExprsPtr<'a>,
        major : ExprPtr<'a>,
        rr_name : NamePtr<'a>,
        rr_n_fields : u16,
        rr_val : ExprPtr<'a>,
        major_args_len : usize,
        r6 : ExprPtr<'a>,
        r7 : ExprPtr<'a>,
        r8 : ExprPtr<'a>,
        r9 : ExprPtr<'a>,
        #[result]
        r10 : ExprPtr<'a>,
        base_const : ExprPtr<'a>,
        major_unredA : ExprPtr<'a>,
        major_fun : ExprPtr<'a>,
        got_rec_rule : RecRulePtr<'a>,
        skip1 : ExprsPtr<'a>,
        skip2 : ExprsPtr<'a>,
        take1 : ExprsPtr<'a>,
        take2 : ExprsPtr<'a>,
        recursor : DeclarPtr<'a>,
        h1 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarPtr<'a>),
        h2 : Step<ToCtorWhenKZst>,
        h3 : Step<WhnfZst>,
        h4 : Step<UnfoldAppsAuxZst>,
        h5 : Step<GetRecRuleZst>,
        h6 : Step<SubstEZst>,
        h7   : Step<FoldlAppsZst>,
        h8   : Step<FoldlAppsZst>,
        h9   : Step<FoldlAppsZst>,
        h10   : Step<WhnfCoreZst>,
    }
}


#[is_step(tag="WC", result_type = "ExprPtr<'a>", fun = "trace_whnf_core")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfCore<'a> {
    #[S]
    Sort {
        e : ExprPtr<'a>,
        l : LevelPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<WhnfSortZst>,
    },
    #[L]
    Lambda {
        e : ExprPtr<'a>,
        lam : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<WhnfLambdaZst>,
    },
    #[Z]
    Let {
        e : ExprPtr<'a>,
        let_ : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<WhnfLetZst>,
    },
    #[I]
    ReduceQuotLift {
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<ReduceQuotLiftZst>,
    },
    
    #[N]
    ReduceQuotInd {
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<ReduceQuotIndZst>,
    },
    #[R]
    ReduceIndRec {
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<ReduceIndRecZst>,
    },
    #[O]
    Owise {
        #[result]
        e : ExprPtr<'a>,
    }
}

#[is_step(tag="WH", result_type = "ExprPtr<'a>", fun = "trace_whnf")]
#[derive(Debug, Clone, Copy)]
pub enum Whnf<'a> {
    #[O]
    CoreOnly {
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<WhnfCoreZst>,
    },
    #[U]
    Unfolding {
        e : ExprPtr<'a>,
        cored  : ExprPtr<'a>,
        unfolded : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<UnfoldDefZst>,
        h3 : Step<WhnfZst>,
    }
}

#[is_step(tag="UD", result_type = "ExprPtr<'a>", fun = "trace_unfold_def")]
#[derive(Debug, Clone, Copy)]
pub enum UnfoldDef<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_val : ExprPtr<'a>,
        d_val_prime : ExprPtr<'a>,
        #[result]
        unfolded : ExprPtr<'a>,
        base : ExprPtr<'a>,
        d_view : DeclarView<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarView<'a>),
        h3 : Step<SubstEZst>,
        h4 : Step<FoldlAppsZst>,
    },
}

#[is_step(tag="SZ", fun = "trace_is_sort_zero")]
#[derive(Debug, Clone, Copy)]
pub enum IsSortZero<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        z : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
    }
}

#[is_step(tag="PR", result_type = "ExprPtr<'a>", fun = "trace_is_proposition")]
#[derive(Debug, Clone, Copy)]
pub enum IsProposition<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        #[result]
        infd : ExprPtr<'a>,
        h1 : Step<InferZst>,
        h2 : Step<IsSortZeroZst>,
    }
}

#[is_step(tag="PF", result_type = "ExprPtr<'a>", fun = "trace_is_proof")]
#[derive(Debug, Clone, Copy)]
pub enum IsProof<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        #[result]
        infd : ExprPtr<'a>,
        h1 : Step<InferZst>,
        h2 : Step<IsPropositionZst>,
    }
}


#[is_step(tag="IR", result_type = "EqResult", fun = "trace_proof_irrel_eq")]
#[derive(Debug, Clone, Copy)]
pub enum ProofIrrelEq<'a> {
    #[B]
    Base {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_type : ExprPtr<'a>,
        r_type : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<IsProofZst>,
        h2 : Step<IsProofZst>,
        h3 : Step<DefEqZst>,
    }
}



#[is_step(tag="LD", result_type = "DeltaResult<'a>", fun = "trace_lazy_delta_step")]
#[derive(Debug, Clone, Copy)]
pub enum LazyDeltaStep<'a> {
    #[R]
    Refl {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
    },
    #[S]
    Sort {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<DefEqSortZst>,
    },
    #[P]
    Pi {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        
        h1 : Step<DefEqPiZst>,
    },
    #[L]
    Lambda {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<DefEqLambdaZst>,
    },
    #[NN]
    NoneNone {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
    },
    #[UL]
    UnfoldingLeft {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_defval_unred : ExprPtr<'a>,
        l_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<UnfoldDefZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
    },
    #[UR]
    UnfoldingRight {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        r_defval_unred : ExprPtr<'a>,
        r_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<UnfoldDefZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
    },
    #[E]
    Extensional {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        c_name : NamePtr<'a>,
        lc_levels : LevelsPtr<'a>,
        rc_levels : LevelsPtr<'a>,
        l_args : ExprsPtr<'a>,
        r_args : ExprsPtr<'a>,
        l_const : ExprPtr<'a>,
        r_const : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<UnfoldAppsAuxZst>,
        h3 : Step<ArgsEqAuxZst>,
        h4 : Step<EqAntisymmManyZst>,
    },
    #[UB]
    UnfoldingBoth {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_defval_unred : ExprPtr<'a>,
        r_defval_unred : ExprPtr<'a>,
        l_defval : ExprPtr<'a>,
        r_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<UnfoldDefZst>,
        h2 : Step<UnfoldDefZst>,
        h3 : Step<WhnfCoreZst>,
        h4 : Step<WhnfCoreZst>,
        h5 : Step<LazyDeltaStepZst>,
    }
}

#[is_step(tag="EQ", result_type = "EqResult", fun = "trace_def_eq")]
#[derive(Debug, Clone, Copy)]
pub enum DefEq<'a> {
    #[R]
    PtrEq {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        #[result]
        result : EqResult
    },
    #[S]
    Sort {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<DefEqSortZst>,
    },
    #[P]
    Pi {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<DefEqPiZst>,
    },
    #[P]
    Lambda {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<DefEqLambdaZst>,
    },
    #[I]
    ProofIrrelEq {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<ProofIrrelEqZst>,
    },
    #[D]
    DeltaShort {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
    },
    #[C]
    Const {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        l_d : ExprPtr<'a>,
        r_d : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
        h4 : Step<DefEqConstZst>,
    },
    #[X]
    Local {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        l_d : ExprPtr<'a>,
        r_d : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
        h4 : Step<DefEqLocalZst>,
    },
    #[A]
    App {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        l_d : ExprPtr<'a>,
        r_d : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
        h4 : Step<DefEqAppZst>,
    },
    #[U]
    EtaLr {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        l_d : ExprPtr<'a>,
        r_d : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
        h4 : Step<DefEqEtaZst>,
    },
    #[V]
    EtaRl {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_w : ExprPtr<'a>,
        r_w : ExprPtr<'a>,
        l_d : ExprPtr<'a>,
        r_d : ExprPtr<'a>,
        
        #[result]
        result : EqResult,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<WhnfCoreZst>,
        h3 : Step<LazyDeltaStepZst>,
        h4 : Step<DefEqEtaZst>,
    },
}

#[is_step(tag="ES", result_type = "EqResult", fun = "trace_def_eq_sort")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqSort<'a> {
    #[B]
    Base {
        l1 : LevelPtr<'a>,
        l2 : LevelPtr<'a>,
        e1 : ExprPtr<'a>,
        e2 : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<EqAntisymmZst>,
    }
}


#[is_step(tag="EL", result_type = "EqResult", fun = "trace_def_eq_lambda")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqLambda<'a> {
    #[B]
    Base {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        doms : ExprsPtr<'a>,
        l_prime : ExprPtr<'a>,
        r_prime : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
    },
    #[E]
    Step {
        ln : NamePtr<'a>,
        rn : NamePtr<'a>,
        lt : ExprPtr<'a>,
        rt : ExprPtr<'a>,
        ls : BinderStyle,
        rs : BinderStyle,
        lb : ExprPtr<'a>,
        rb : ExprPtr<'a>,
        lt_prime : ExprPtr<'a>,
        rt_prime : ExprPtr<'a>,
        doms : ExprsPtr<'a>,
        serial : LocalSerial,
        local : ExprPtr<'a>,
        doms_prime : ExprsPtr<'a>,
        e1 : ExprPtr<'a>,
        e2 : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<DefEqLambdaZst>,
    }    
}

#[is_step(tag="EP", result_type = "EqResult", fun = "trace_def_eq_pi")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqPi<'a> {
    #[B]
    Base {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        doms : ExprsPtr<'a>,
        l_prime : ExprPtr<'a>,
        r_prime : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
    },
    #[E]
    Step {
        ln : NamePtr<'a>,
        rn : NamePtr<'a>,
        lt : ExprPtr<'a>,
        rt : ExprPtr<'a>,
        ls : BinderStyle,
        rs : BinderStyle,
        lb : ExprPtr<'a>,
        rb : ExprPtr<'a>,
        lt_prime : ExprPtr<'a>,
        rt_prime : ExprPtr<'a>,
        doms : ExprsPtr<'a>,
        serial : LocalSerial,
        local : ExprPtr<'a>,
        doms_prime : ExprsPtr<'a>,
        e1 : ExprPtr<'a>,
        e2 : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<DefEqPiZst>,
    }    
}


#[is_step(tag="FX", result_type = "EqResult", fun = "trace_args_eq_aux")]
#[derive(Debug, Clone, Copy)]
pub enum ArgsEqAux<'a> {
    #[B]
    Base {
        l : ExprsPtr<'a>,
        r : ExprsPtr<'a>,
        #[result]
        result : EqResult,
    },
    #[S]
    Step {
        l_hd  : ExprPtr<'a>,
        r_hd  : ExprPtr<'a>,
        l_tl : ExprsPtr<'a>,
        r_tl : ExprsPtr<'a>,
        l : ExprsPtr<'a>,
        r : ExprsPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<DefEqZst>,
        h2 : Step<ArgsEqAuxZst>,
    }
}

#[is_step(tag="EC", result_type = "EqResult", fun = "trace_def_eq_const")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqConst<'a> {
    #[B]
    Base {
        l_name : NamePtr<'a>,
        r_name : NamePtr<'a>,
        l_levels : LevelsPtr<'a>,
        r_levels : LevelsPtr<'a>,
        e1  : ExprPtr<'a>,
        e2 : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<EqAntisymmManyZst>,
    }
}


#[is_step(tag="EX", result_type = "EqResult", fun = "trace_def_eq_local")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqLocal<'a> {
    #[B]
    Base {
        ln : NamePtr<'a>,
        rn : NamePtr<'a>,
        lt : ExprPtr<'a>,
        rt : ExprPtr<'a>,
        ls : BinderStyle,
        rs : BinderStyle,
        l_serial : LocalSerial,
        r_serial : LocalSerial,
        e : ExprPtr<'a>,
        #[result]
        result : EqResult,
    }
}

#[is_step(tag="EA", result_type = "EqResult", fun = "trace_def_eq_app")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqApp<'a> {
    #[B]
    Base {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_fun : ExprPtr<'a>,
        r_fun : ExprPtr<'a>,
        l_args : ExprsPtr<'a>,
        r_args : ExprsPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<UnfoldAppsAuxZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<ArgsEqAuxZst>,
    }
}

#[is_step(tag="ET", result_type = "EqResult", fun = "trace_def_eq_eta")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqEta<'a> {
    #[B]
    Base {
        r : ExprPtr<'a>,
        ln : NamePtr<'a>,
        rn : NamePtr<'a>,
        lt : ExprPtr<'a>,
        rt : ExprPtr<'a>,        
        ls : BinderStyle,
        rs : BinderStyle,
        lb : ExprPtr<'a>,
        rb : ExprPtr<'a>,
        r_type_unred : ExprPtr<'a>,
        r_type_red : ExprPtr<'a>,
        l_lambda : ExprPtr<'a>,
        r_lambda : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InferZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<DefEqZst>,
    }
}





#[is_step(tag="ENS", result_type = "LevelPtr<'a>", fun = "trace_ensure_sort")]
#[derive(Debug, Clone, Copy)]
pub enum EnsureSort<'a> {
    #[B]
    Base {
        #[result]
        level : LevelPtr<'a>,
        e : ExprPtr<'a>,
    },
    #[R]
    Reduce {
        e : ExprPtr<'a>,
        #[result]
        level : LevelPtr<'a>,
        e_prime : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
    }
}




#[is_step(tag="ENT", result_type = "LevelPtr<'a>", fun = "trace_ensure_type")]
#[derive(Debug, Clone, Copy)]
pub enum EnsureType<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        e_type : ExprPtr<'a>,
        #[result]
        sort_level : LevelPtr<'a>,
        h1 : Step<InferZst>,
        h2 : Step<EnsureSortZst>,
    },
}


#[is_step(tag="ENP", result_type = "ExprPtr<'a>", fun = "trace_ensure_pi")]
#[derive(Debug, Clone, Copy)]
pub enum EnsurePi<'a> {
    #[B]
    Base {
        #[result]
        e : ExprPtr<'a>,
        h1 : Step<IsPiZst>,
    },
    #[R]
    Reduce {
        e : ExprPtr<'a>,
        #[result]
        reduced : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<IsPiZst>,
    }
}



#[is_step(tag="IN", result_type = "ExprPtr<'a>", fun = "trace_infer")]
#[derive(Debug, Clone, Copy)]
pub enum Infer<'a> {
    #[S]
    Sort {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferSortZst>,
    },
    #[C]
    Const {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferConstZst>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<InferZst>,
        h3 : Step<InferAppZst>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[P]
    Pi {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferPiZst>,
    },
    #[L]
    Lambda {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferLambdaZst>,
    },
    #[Z]
    Let {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferLetZst>,
    },
    #[X]
    Local {
        e : ExprPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferLocalZst>,
    }
}

#[is_step(tag="IS", result_type = "ExprPtr<'a>", fun = "trace_infer_sort")]
#[derive(Debug, Clone, Copy)]
pub enum InferSort<'a> {
    #[I]
    InferOnly {
        l : LevelPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
    },
    #[C]
    Checked {
        l : LevelPtr<'a>,
        e : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
    }
}

#[is_step(tag="IC", result_type = "ExprPtr<'a>", fun = "trace_infer_const")]
#[derive(Debug, Clone, Copy)]
pub enum InferConst<'a> {
    #[I]
    InferOnly {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_val : Option<ExprPtr<'a>>,
        #[result]
        inferred : ExprPtr<'a>,
        flag : InferFlag,
        e : ExprPtr<'a>,
        declar_view : DeclarView<'a>,
        h1 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarView<'a>),
        h2 : Step<SubstEZst>,
    },
    #[C]
    Checked {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        tc_uparams : LevelsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_val : Option<ExprPtr<'a>>,
        #[result]
        inferred : ExprPtr<'a>,
        flag : InferFlag,
        e : ExprPtr<'a>,
        declar_view : DeclarView<'a>,
        h1 : (NamePtr<'a>, Step<AdmitDeclarZst>, DeclarView<'a>),
        h2 : Step<ParamsDefinedManyZst>,
        h3 : Step<SubstEZst>,
    }
}



#[is_step(tag="INA", result_type = "ExprPtr<'a>", fun = "trace_infer_app")]
#[derive(Debug, Clone, Copy)]
pub enum InferApp<'a> {
    #[B]
    Base {
        e_type : ExprPtr<'a>,
        context : ExprsPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InstZst>,
        ind_arg2 : ExprsPtr<'a>,
    },
    #[PI]
    StepPiInferOnly {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        hd : ExprPtr<'a>,
        args_tl : ExprsPtr<'a>,
        context : ExprsPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        e : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        context_prime : ExprsPtr<'a>,
        h1 : Step<InferAppZst>,
    },
    #[PC]
    StepPiChecked {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        hd_arg : ExprPtr<'a>,
        tl_args : ExprsPtr<'a>,
        context : ExprsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        arg_type : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        e : ExprPtr<'a>,
        context_prime : ExprsPtr<'a>,
        args : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<InferAppZst>,
    },
    #[SN]
    StepNotPi {
        e : ExprPtr<'a>,
        e_prime : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        context : ExprsPtr<'a>,
        flag : InferFlag,
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        as_pi : ExprPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<EnsurePiZst>,
        h3 : Step<InferAppZst>,
    }
}


#[is_step(tag="ISO", result_type = "LevelPtr<'a>", fun = "trace_infer_sort_of")]
#[derive(Debug, Clone, Copy)]
pub enum InferSortOf<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        inferred : ExprPtr<'a>,
        #[result]
        level : LevelPtr<'a>,
        e_prime : ExprPtr<'a>,
        h1 : Step<InferZst>,
        h2 : Step<WhnfZst>,
    }
}

#[is_step(tag="NP", result_type = "ExprPtr<'a>", fun = "trace_infer_pi")]
#[derive(Debug, Clone, Copy)]
pub enum InferPi<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        local_binders : ExprsPtr<'a>,
        levels : LevelsPtr<'a>,
        flag : InferFlag,
        instd : ExprPtr<'a>,
        inferred_level : LevelPtr<'a>,
        folded : LevelPtr<'a>,
        h1 : Step<IsPiZst>,
        h2 : Step<InstZst>,
        h3 : Step<InferSortOfZst>,
        h4 : Step<FoldImaxsZst>,
        #[result]
        ind_arg5 : ExprPtr<'a>,
    },
    #[S]
    Step {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        local_binders : ExprsPtr<'a>,
        levels : LevelsPtr<'a>,
        flag : InferFlag,
        #[result]
        inferred : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        inferred_level : LevelPtr<'a>,
        serial : LocalSerial,
        e : ExprPtr<'a>,
        levelsA : LevelsPtr<'a>,
        local : ExprPtr<'a>,
        localsA : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferSortOfZst>,
        h3 : Step<InferPiZst>,
    }
}


#[is_step(tag="FO", result_type = "ExprPtr<'a>", fun = "trace_fold_pis_once")]
#[derive(Debug, Clone, Copy)]
pub enum FoldPisOnce<'a> {
    #[B]
    Base {
        #[result]
        out : ExprPtr<'a>,
        b_types : ExprsPtr<'a>,
        local_binders : ExprsPtr<'a>,
    },
    #[S]
    Step {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        body : ExprPtr<'a>,
        serial : LocalSerial,
        ts : ExprsPtr<'a>,
        unused_t : ExprPtr<'a>,
        local_binders : ExprsPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        local_binders_prime : ExprsPtr<'a>,
        ts_prime : ExprsPtr<'a>,
        folded_pi : ExprPtr<'a>,
        h1 : Step<FoldPisOnceZst>,
    }
}

#[is_step(tag="IL", result_type = "ExprPtr<'a>", fun = "trace_infer_lambda")]
#[derive(Debug, Clone, Copy)]
pub enum InferLambda<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        local_binders : ExprsPtr<'a>,
        b_types : ExprsPtr<'a>,
        flag : InferFlag,
        instd : ExprPtr<'a>,
        inferred_inner : ExprPtr<'a>,
        abstrd : ExprPtr<'a>,
        #[result]
        folded : ExprPtr<'a>,
        h1 : Step<IsLambdaZst>,
        h2 : Step<InstZst>,
        h3 : Step<InferZst>,
        h4 : Step<AbstrZst>,
        h5 : Step<FoldPisOnceZst>,
    },
    #[I]
    StepInferOnly {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_types : ExprsPtr<'a>,
        local_binders : ExprsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        serial : LocalSerial,
        e : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        b_typesA : ExprsPtr<'a>,
        localsA : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferLambdaZst>,

    },
    #[C]
    StepChecked {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_types : ExprsPtr<'a>,
        local_binders : ExprsPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        b_type_sort : LevelPtr<'a>,
        serial : LocalSerial,
        e : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        b_typesA : ExprsPtr<'a>,
        localsA : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferSortOfZst>, 
        h3 : Step<InferLambdaZst>,

    },
}



#[is_step(tag="INZ", result_type = "ExprPtr<'a>", fun = "trace_infer_let")]
#[derive(Debug, Clone, Copy)]
pub enum InferLet<'a> {
    #[I]
    InferOnly {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        flag : InferFlag,
        b_prime : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        e : ExprPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferZst>,
    },
    #[C]
    Checked {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body : ExprPtr<'a>,
        flag : InferFlag,
        b_type_sort : LevelPtr<'a>,
        val_type : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        e : ExprPtr<'a>,
        h1 : Step<InferSortOfZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<InstZst>,
        h5 : Step<InferZst>,
    }
}


#[is_step(tag="IX", result_type = "ExprPtr<'a>", fun = "trace_infer_local")]
#[derive(Debug, Clone, Copy)]
pub enum InferLocal<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        n : NamePtr<'a>,
        #[result]
        t : ExprPtr<'a>,
        s : BinderStyle,
    }
}


#[is_step(tag="LPS", result_type = "ExprsPtr<'a>", fun = "trace_mk_local_params")]
#[derive(Debug, Clone, Copy)]
pub enum MkLocalParams<'a> {
    #[B]
    Base {
        ind_type_cursor : ExprPtr<'a>,
        num_params : u16,
        #[result]
        params : ExprsPtr<'a>,
    },
    #[S]
    Step {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        num_params : u16,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        params_tl : ExprsPtr<'a>,
        ind_type_cursor : ExprPtr<'a>,
        num_params_prime : u16,
        params_hd : ExprPtr<'a>,
        #[result]
        params : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<MkLocalParamsZst>,
    }
}


#[is_step(
    tag="HT", 
    result_type = "(ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>)", 
    fun = "trace_handle_telescope1"
)]
#[derive(Debug, Clone, Copy)]
pub enum HandleTelescope1<'a> {
    #[B]
    Base {
        indblock : IndBlockPtr,
        ind_name : NamePtr<'a>,
        codom_level : LevelPtr<'a>,
        //
        ind_type_cursor : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ind_const : ExprPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),
        h1 : Step<IsPiZst>,
        h2 : Step<EnsureSortZst>,
    },
    #[I]
    StepIndex {
        indblock : IndBlockPtr,
        ind_name : NamePtr<'a>,
        codom_level : LevelPtr<'a>,
        //
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        indices_tl : ExprsPtr<'a>,
        b_prime : ExprPtr<'a>,
        //
        ind_type_cursor : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        indices_hd : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        rec_result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),
        #[result]
        result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),
        h1 : Step<InstZst>,
        h2 : Step<HandleTelescope1Zst>,
    },
    #[P]
    StepParam {
        indblock : IndBlockPtr,
        ind_name : NamePtr<'a>,
        codom_level : LevelPtr<'a>,
        //
        n : NamePtr<'a>,
        t1 : ExprPtr<'a>,
        t2 : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        params_tl : ExprsPtr<'a>,
        b_prime : ExprPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),
        //
        ind_type_cursor : ExprPtr<'a>,
        params_hd : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        h1 : Step<DefEqZst>,
        h2 : Step<InstZst>,
        h3 : Step<HandleTelescope1Zst>,
    }
}


#[is_step(
    tag="HTS", 
    result_type = "(ExprsPtr<'a>, LevelPtr<'a>, ExprsPtr<'a>)", 
    fun = "trace_handle_telescopes"
)]
#[derive(Debug, Clone, Copy)]
pub enum HandleTelescopes<'a> {
    #[B]
    Base {
        indblock : IndBlockPtr,
        params : ExprsPtr<'a>,
        codom_level : LevelPtr<'a>,
        //
        i_ns_hd : NamePtr<'a>,
        i_ts_hd : ExprPtr<'a>,
        indices : ExprsPtr<'a>,
        ind_const : ExprPtr<'a>,
        rec_result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),
        rem_ind_names : NamesPtr<'a>,
        rem_ind_types : ExprsPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, LevelPtr<'a>, ExprsPtr<'a>),
        h1 : Step<HandleTelescope1Zst>,
    },
    #[I]
    Step {
        indblock : IndBlockPtr,
        params : ExprsPtr<'a>,
        codom_level : LevelPtr<'a>,
        //
        i_ns_hd : NamePtr<'a>,
        i_ns_tl : NamesPtr<'a>,
        i_ts_hd : ExprPtr<'a>,
        i_ts_tl : ExprsPtr<'a>,
        indices_r : ExprsPtr<'a>,
        indices_l : ExprsPtr<'a>,
        codom_level2 : LevelPtr<'a>,
        ind_cs_tl : ExprsPtr<'a>,
        ind_cs_hd : ExprPtr<'a>,
        ind_cs : ExprsPtr<'a>,
        rec_result : (ExprsPtr<'a>, LevelPtr<'a>, ExprsPtr<'a>),       
        hd_result : (ExprsPtr<'a>, LevelPtr<'a>, ExprPtr<'a>),       
        indices : ExprsPtr<'a>,
        rem_ind_names : NamesPtr<'a>,
        rem_ind_types : ExprsPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, LevelPtr<'a>, ExprsPtr<'a>),       
        h1 : Step<HandleTelescopesZst>,
        h2 : Step<HandleTelescope1Zst>,
        h3 : Step<EqAntisymmZst>,
    },
}


#[is_step(tag="CI", fun = "trace_check_ind_types")]
#[derive(Debug, Clone, Copy)]
pub enum CheckIndTypes<'a> {
    #[B]
    Base {
        indblock : IndBlockPtr,
        params : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        codom_level : LevelPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ind_types_hd : ExprPtr<'a>,
        ind_types_tl : ExprsPtr<'a>,
        telescopes_result : (ExprsPtr<'a>, LevelPtr<'a>, ExprsPtr<'a>),
        h1 : Step<MkLocalParamsZst>,
        h2 : Step<HandleTelescopesZst>,
    }
}


#[is_step(tag="MIT", result_type = "DeclarsPtr<'a>", fun = "trace_mk_ind_types")]
#[derive(Debug, Clone, Copy)]
pub enum MkIndTypes<'a> {
    #[B]
    Base {
        indblock : IndBlockPtr,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        #[result]
        declars : DeclarsPtr<'a>,

    },
    #[S]
    Step {
        indblock : IndBlockPtr,
        i_ns_hd : NamePtr<'a>,
        i_ns_tl : NamesPtr<'a>,
        i_ts_hd : ExprPtr<'a>,
        i_ts_tl : ExprsPtr<'a>,
        ctor_names_curr : NamesPtr<'a>,
        ctor_names_rest : NamesPtr<'a>,
        declars_tl : DeclarsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        declars_hd : DeclarPtr<'a>,
        #[result]
        declars : DeclarsPtr<'a>,
        h1 : Step<MkIndTypesZst>,
    }
}




#[is_step(tag="VP", result_type = "bool", fun = "trace_valid_param_apps")]
#[derive(Debug, Clone, Copy)]
pub enum ValidParamApps<'a> {
    #[B]
    Base {
        rem_ind_apps : ExprsPtr<'a>,
        rem_block_params : ExprsPtr<'a>,
        #[result]
        b : bool
    },
    #[S]
    Step {
        hd : ExprPtr<'a>,
        ind_apps_tl : ExprsPtr<'a>,
        block_params_tl : ExprsPtr<'a>,
        rem_ind_apps : ExprsPtr<'a>,
        rem_block_params : ExprsPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<ValidParamAppsZst>,
    }
}

#[is_step(tag="VA", result_type = "bool", fun = "trace_is_valid_ind_app")]
#[derive(Debug, Clone, Copy)]
pub enum IsValidIndApp<'a> {
    #[F]
    BaseFf {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        stripped_ctor_type : ExprPtr<'a>,
        unfolded_fun : ExprPtr<'a>,
        ind_apps : ExprsPtr<'a>,
        apps_len : u16,
        telescope_size : u16,
        b1 : bool,
        b2 : bool,
        #[result]
        b : bool,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<TelescopeSizeZst>,
    },
    #[T]
    BaseTt {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        stripped_ctor_type : ExprPtr<'a>,
        unfolded_fun : ExprPtr<'a>,
        ind_apps : ExprsPtr<'a>,
        apps_len : u16,
        telescope_size : u16,
        b1 : bool,
        b2 : bool,
        b3 : bool,
        #[result]
        b : bool,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<TelescopeSizeZst>,
        h3 : Step<ValidParamAppsZst>,
    }
}


#[is_step(tag="WV", result_type = "u16", fun = "trace_which_valid_ind_app")]
#[derive(Debug, Clone, Copy)]
pub enum WhichValidIndApp<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        u_i_ty : ExprPtr<'a>,
        ind_types_hd : ExprPtr<'a>,
        ind_types_tl : ExprsPtr<'a>,
        ind_consts_hd : ExprPtr<'a>,
        ind_consts_tl : ExprsPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        #[result]
        ind_ty_idx : u16,
        h1 : Step<IsValidIndAppZst>,
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        u_i_ty : ExprPtr<'a>,
        ind_types_hd : ExprPtr<'a>,
        ind_types_tl : ExprsPtr<'a>,
        ind_consts_hd : ExprPtr<'a>,
        ind_consts_tl : ExprsPtr<'a>,
        #[result]
        ind_ty_idx : u16,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ind_ty_idx_prime : u16,
        h1 : Step<IsValidIndAppZst>,
        h2 : Step<WhichValidIndAppZst>,
    }
}


#[is_step(tag="IRA", result_type = "bool", fun = "trace_is_rec_argument")]
#[derive(Debug, Clone, Copy)]
pub enum IsRecArgument<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        ctor_arg : ExprPtr<'a>,
        ctor_arg_prime : ExprPtr<'a>,
        #[result]
        result : bool,
        h1 : Step<WhnfZst>,
        h2 : Step<IsValidIndAppZst>,
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        ctor_arg_prime : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        #[result]
        result : bool,
        ctor_arg : ExprPtr<'a>,
        local : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<InstZst>,
        h3 : Step<IsRecArgumentZst>,
    },
}


#[is_step(tag="CKP", fun = "trace_check_positivity1")]
#[derive(Debug, Clone, Copy)]
pub enum CheckPositivity1<'a> {
    #[U]
    ByUnsafe {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_type : ExprPtr<'a>,
    },
    #[N]
    NoIndOccs {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_type : ExprPtr<'a>,
        ctor_type_prime : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<HasIndOccZst>,
    },
    #[V]
    BaseValid {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_type : ExprPtr<'a>,
        ctor_type_prime : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<IsValidIndAppZst>,
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        ctor_type : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        ctor_type_prime : ExprPtr<'a>,
        local : ExprPtr<'a>,
        h1 : Step<WhnfZst>,
        h2 : Step<HasIndOccZst>,
        h3 : Step<InstZst>,
        h4 : Step<CheckPositivity1Zst>,
    }
}


#[is_step(tag="CC", fun = "trace_check_ctor1")]
#[derive(Debug, Clone, Copy)]
pub enum CheckCtor1<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        ctor_type : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        h1 : Step<IsValidIndAppZst>,
    },
    #[Z]
    StepProp {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        sort_level : LevelPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        h1 : Step<CheckPositivity1Zst>,
        h2 : Step<EnsureTypeZst>,
        h3 : Step<IsZeroZst>,
        h4 : Step<InstZst>,
        h5 : Step<CheckCtor1Zst>,
    },
    #[L]
    StepLe {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        sort_level : LevelPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        h1 : Step<CheckPositivity1Zst>,
        h2 : Step<EnsureTypeZst>,
        h3 : Step<LeqZst>,
        h4 : Step<InstZst>,
        h5 : Step<CheckCtor1Zst>,
    },
    #[P]
    StepParam {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        p_n : NamePtr<'a>,
        p_t : ExprPtr<'a>,
        p_s : BinderStyle,
        serial : LocalSerial,
        params_tl : ExprsPtr<'a>,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        ps_hd : ExprPtr<'a>,
        ps : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        h1 : Step<DefEqZst>,
        h2 : Step<InstZst>,
        h3 : Step<CheckCtor1Zst>,
    }
}


#[is_step(tag="MCG", result_type = "DeclarsPtr<'a>", fun = "trace_mk_ctor_group1")]
#[derive(Debug, Clone, Copy)]
pub enum MkCtorGroup1<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        #[result]
        ds : DeclarsPtr<'a>,

    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        //
        ns_hd : NamePtr<'a>,
        ns_tl : NamesPtr<'a>,
        ts_hd : ExprPtr<'a>,
        ts_tl : ExprsPtr<'a>,
        telescope_size : u16,
        ds_tl : DeclarsPtr<'a>,
        num_fields : u16,
        d : DeclarPtr<'a>,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        #[result]
        ds : DeclarsPtr<'a>,
        h1 : Step<MkCtorGroup1Zst>,
        h2 : Step<TelescopeSizeZst>,
        h3 : Step<CheckCtor1Zst>,
    }
}


#[is_step(tag="MCS", result_type = "DeclarsPtr<'a>", fun = "trace_mk_ctors")]
#[derive(Debug, Clone, Copy)]
pub enum MkCtors<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        //
        rem_ind_names : NamesPtr<'a>,
        rem_ind_types : ExprsPtr<'a>,
        rem_ind_consts : ExprsPtr<'a>,
        rem_c_names : NamesPtr<'a>,
        rem_c_types : ExprsPtr<'a>,
        #[result]
        ds : DeclarsPtr<'a>,

    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        //
        ind_n_hd : NamePtr<'a>,
        ind_n_tl : NamesPtr<'a>,
        ind_t_hd : ExprPtr<'a>,
        ind_t_tl : ExprsPtr<'a>,
        ind_c_hd : ExprPtr<'a>,
        ind_c_tl : ExprsPtr<'a>,
        curr_c_ns : NamesPtr<'a>,
        rest_c_ns : NamesPtr<'a>,
        curr_c_ts : ExprsPtr<'a>,
        rest_c_ts : ExprsPtr<'a>,
        curr_ds : DeclarsPtr<'a>,
        rest_ds : DeclarsPtr<'a>,

        rem_ind_names : NamesPtr<'a>,
        rem_ind_types : ExprsPtr<'a>,
        rem_ind_consts : ExprsPtr<'a>,
        rem_c_names : NamesPtr<'a>,
        rem_c_types : ExprsPtr<'a>,
        #[result]
        ds : DeclarsPtr<'a>,
        h1 : Step<MkCtorsZst>,
        h2 : Step<MkCtorGroup1Zst>,
    }
}


#[is_step(tag="DCS", fun = "trace_declare_ctors")]
#[derive(Debug, Clone, Copy)]
pub enum DeclareCtors {
    #[B]
    Base {
        h1 : Step<MkCtorsZst>
    }
}


#[is_step(tag="LEA", result_type = "bool", fun = "trace_large_elim_test_aux")]
#[derive(Debug, Clone, Copy)]
pub enum LargeElimTestAux<'a> {
    #[B]
    Base {
        ctor_type : ExprPtr<'a>,
        ctor_fun : ExprPtr<'a>,
        ctor_args : ExprsPtr<'a>,
        nonzero_ctor_args : ExprsPtr<'a>,
        #[result]
        large_eliminating : bool,
        params_rem : u16,
        h1 : Step<IsPiZst>,
        h2 : Step<UnfoldAppsAuxZst>,
        h3 : Step<IsSubsetZst>,
    },
    #[Z]
    StepZero {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        t_level : LevelPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        nonzero_ctor_args : ExprsPtr<'a>,
        #[result]
        large_eliminating : bool,
        params_rem : u16,
        ctor_type : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        h1 : Step<EnsureTypeZst>,
        h2 : Step<IsZeroZst>,
        h3 : Step<InstZst>,
        h4 : Step<LargeElimTestAuxZst>,
    },
    #[N]
    StepNonzero {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        t_level : LevelPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        nonzero_ctor_args : ExprsPtr<'a>,
        #[result]
        large_eliminating : bool,
        params_rem : u16,
        ctor_type : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        h1 : Step<EnsureTypeZst>,
        h2 : Step<IsZeroZst>,
        h3 : Step<InstZst>,
        h4 : Step<LargeElimTestAuxZst>,
    },
    #[P]
    StepParam {
        params_rem : u16,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        #[result]
        large_eliminating : bool,
        params_rem_prime : u16,
        ctor_type : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        nonzero_ctor_args : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<LargeElimTestAuxZst>,
    }


}


#[is_step(tag="LET", result_type = "bool", fun = "trace_large_elim_test")]
#[derive(Debug, Clone, Copy)]
pub enum LargeElimTest<'a> {
    #[N]
    Nonzero {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        large_eliminating : bool,
        h1 : Step<IsNonzeroZst>,
    },
    #[M]
    IsMutual {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        large_eliminating : bool,
        h1 : Step<IsNonzeroZst>,
    },
    #[C]
    ManyCtors {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        large_eliminating : bool,
        h1 : Step<IsNonzeroZst>,
    },
    #[X]
    NoCtors {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        large_eliminating : bool
    },
    #[A]
    ByAux {
        checked_indblock : CheckedIndBlockPtr,
        ctor_type : ExprPtr<'a>,
        #[result]
        large_eliminating : bool,
        h1 : Step<IsNonzeroZst>,
        h2 : Step<LargeElimTestAuxZst>,
    }
}

#[is_step(tag="ME", result_type = "LevelPtr<'a>", fun = "trace_mk_elim_level")]
#[derive(Debug, Clone, Copy)]
pub enum MkElimLevel<'a> {
    #[L]
    Large {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        elim_level : LevelPtr<'a>,
        h1 : Step<LargeElimTestZst>,
        h2 : Step<PosZst>,
    },
    #[S]
    Small {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        elim_level : LevelPtr<'a>,
        h1 : Step<LargeElimTestZst>,
    
    }
}


#[is_step(tag="KTA", result_type = "bool", fun = "trace_init_k_target_aux")]
#[derive(Debug, Clone, Copy)]
pub enum InitKTargetAux<'a> {
    #[B]
    Base {
        ctor_type : ExprPtr<'a>,
        is_pi : bool,
        params_rem : u16,
        #[result]
        k_target : bool,
        h1 : Step<IsPiZst>
    },
    #[S]
    Step {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        params_rem : u16,
        #[result]
        k_target : bool,
        ctor_type : ExprPtr<'a>,
        params_rem_prime : u16,
        h1 : Step<InitKTargetAuxZst>,
    }
}


#[is_step(tag="KT", result_type = "bool", fun = "trace_init_k_target")]
#[derive(Debug, Clone, Copy)]
pub enum InitKTarget<'a> {
    #[M]
    IsMutual {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        k_target : bool,
    },
    #[N]
    Nonzero {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        k_target : bool,
        h1 : Step<IsZeroZst>,
    },
    #[O]
    NotOneCtor {
        checked_indblock : CheckedIndBlockPtr,
        #[result]
        k_target : bool,
    },
    #[A]
    ByAux {
        checked_indblock : CheckedIndBlockPtr,
        ctor_type : ExprPtr<'a>,
        #[result]
        k_target : bool,
        h1 : Step<InitKTargetAuxZst>,
    }
    
}


#[is_step(tag="MJA", result_type = "ExprsPtr<'a>", fun = "trace_mk_majors_aux")]
#[derive(Debug, Clone, Copy)]
pub enum MkMajorsAux<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        indices : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        #[result]
        majors : ExprsPtr<'a>
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        indices_l : ExprsPtr<'a>,
        indices_r : ExprsPtr<'a>,
        ind_consts_hd : ExprPtr<'a>,
        ind_consts_tl : ExprsPtr<'a>,
        majors_tl : ExprsPtr<'a>,
        major_typeA : ExprPtr<'a>,
        major_typeB : ExprPtr<'a>,
        serial : LocalSerial,
        indices : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        major_name : NamePtr<'a>,
        major_bstyle : BinderStyle,
        majors_hd : ExprPtr<'a>,
        #[result]
        majors : ExprsPtr<'a>,
        h1 : Step<MkMajorsAuxZst>,
        h2 : Step<FoldlAppsZst>,
        h3 : Step<FoldlAppsZst>,
    }

}


#[is_step(tag="MKC", result_type = "ExprPtr<'a>", fun = "trace_mk_motive")]
#[derive(Debug, Clone, Copy)]
pub enum MkMotive<'a> {
    #[I]
    Indep {
        elim_level : LevelPtr<'a>,
        indices : ExprsPtr<'a>,
        ind_type_idx : u16,
        major : ExprPtr<'a>,
        serial : LocalSerial,
        motive_type : ExprPtr<'a>,
        elim_sort : ExprPtr<'a>,
        motive_name : NamePtr<'a>,
        motive_bstyle : BinderStyle,
        #[result]
        motive : ExprPtr<'a>,
        h1 : Step<FoldPisZst>,
    },
    #[D]
    Dep {
        elim_level : LevelPtr<'a>,
        indices : ExprsPtr<'a>,
        ind_type_idx : u16,
        major : ExprPtr<'a>,
        serial : LocalSerial,
        motive_typeA : ExprPtr<'a>,
        motive_typeB : ExprPtr<'a>,
        elim_sort : ExprPtr<'a>,
        motive_name : NamePtr<'a>,
        motive_bstyle : BinderStyle,
        #[result]
        motive : ExprPtr<'a>,
        h1 : Step<ApplyPiZst>,
        h2 : Step<FoldPisZst>,
    }
}

#[is_step(tag="MCZ", result_type = "ExprsPtr<'a>", fun = "trace_mk_motives")]
#[derive(Debug, Clone, Copy)]
pub enum MkMotives<'a> {
    #[B]
    Base {
        elim_level : LevelPtr<'a>,
        ind_type_idx : u16,
        majors : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        #[result]
        motives : ExprsPtr<'a>,
    },
    #[S]
    Step {
        elim_level : LevelPtr<'a>,
        ind_type_idx : u16,
        majors_hd : ExprPtr<'a>,
        majors_tl : ExprsPtr<'a>,
        indices_l : ExprsPtr<'a>,
        indices_r : ExprsPtr<'a>,
        motives_hd : ExprPtr<'a>,
        motives_tl : ExprsPtr<'a>,
        ind_type_idx_prime : u16,
        majors : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        #[result]
        motives : ExprsPtr<'a>,
        h1 : Step<MkMotivesZst>,
        h2 : Step<MkMotiveZst>,
    },
}



#[is_step(tag="SCA", result_type = "(ExprsPtr<'a>, ExprsPtr<'a>, ExprPtr<'a>)", fun = "trace_sep_rec_ctor_args")]
#[derive(Debug, Clone, Copy)]
pub enum SepRecCtorArgs<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        inner_type : ExprPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, ExprsPtr<'a>, ExprPtr<'a>)
    },
    #[N]
    NonrecArg {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        inner_type : ExprPtr<'a>,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        all_args_tl : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, ExprsPtr<'a>, ExprPtr<'a>),
        h1 : Step<InstZst>,
        h2 : Step<SepRecCtorArgsZst>,
        h3 : Step<IsRecArgumentZst>,
    },
    #[R]
    RecArg {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        inner_type : ExprPtr<'a>,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        all_args_tl : ExprsPtr<'a>,
        rec_args_tl : ExprsPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, ExprsPtr<'a>, ExprPtr<'a>),
        h1 : Step<InstZst>,
        h2 : Step<SepRecCtorArgsZst>,
        h3 : Step<IsRecArgumentZst>,
    },
    #[P]
    Param {
        checked_indblock : CheckedIndBlockPtr,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        inner_type : ExprPtr<'a>,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        rem_params_hd : ExprPtr<'a>,
        rem_params_tl : ExprsPtr<'a>,
        rem_params : ExprsPtr<'a>,
        ctor_type : ExprPtr<'a>,
        #[result]
        result : (ExprsPtr<'a>, ExprsPtr<'a>, ExprPtr<'a>),
        h1 : Step<InstZst>,
        h2 : Step<SepRecCtorArgsZst>,
    }      

}


#[is_step(tag="GI", result_type = "(u16, ExprsPtr<'a>)", fun = "trace_get_i_indices")]
#[derive(Debug, Clone, Copy)]
pub enum GetIIndices<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        type_cursor : ExprPtr<'a>,
        type_fun : ExprPtr<'a>,
        type_args : ExprsPtr<'a>,
        valid_app_idx : u16,
        indices : ExprsPtr<'a>,
        #[result]
        result : (u16, ExprsPtr<'a>),
        h1 : Step<WhichValidIndAppZst>,
        h2 : Step<UnfoldAppsAuxZst>,
    }
}


#[is_step(tag="HRX", result_type = "(ExprPtr<'a>, ExprsPtr<'a>)", fun = "trace_handle_rec_args_aux")]
#[derive(Debug, Clone, Copy)]
pub enum HandleRecArgsAux<'a> {
    #[B]
    Base {
        type_cursor : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        result : (ExprPtr<'a>, ExprsPtr<'a>)
    },
    #[S]
    Step {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        b_prime_red : ExprPtr<'a>,
        inner : ExprPtr<'a>,
        args_tl : ExprsPtr<'a>,
        type_cursor : ExprPtr<'a>,
        local_expr : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        #[result]
        result : (ExprPtr<'a>, ExprsPtr<'a>),
        h1 : Step<InstZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<HandleRecArgsAuxZst>,
    }
}


#[is_step(tag="RAM", result_type = "ExprsPtr<'a>", fun = "trace_handle_rec_args_minor")]
#[derive(Debug, Clone, Copy)]
pub enum HandleRecArgsMinor<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        rem_rec_args : ExprsPtr<'a>,
        #[result]
        result : ExprsPtr<'a>,
    },
    #[I]
    StepIndep {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        self_idx : u16,
        rec_args_hd : ExprPtr<'a>,
        rec_args_tl : ExprsPtr<'a>,
        result_tl : ExprsPtr<'a>,
        u_i_ty : ExprPtr<'a>,
        u_i_ty_red : ExprPtr<'a>,
        inner : ExprPtr<'a>,
        rec_aux_result : ExprsPtr<'a>,
        indices_result : ExprsPtr<'a>,
        valid_pos : u16,
        motive_appA : ExprPtr<'a>,
        v_i_ty : ExprPtr<'a>,
        serial : LocalSerial,
        rec_args : ExprsPtr<'a>,
        self_idx_prime : u16,
        v_name : NamePtr<'a>,
        motive : ExprPtr<'a>,
        result_hd : ExprPtr<'a>,
        #[result]
        result : ExprsPtr<'a>,
        h1 : Step<HandleRecArgsMinorZst>,
        h2 : Step<InferZst>,
        h3 : Step<WhnfZst>,
        h4 : Step<HandleRecArgsAuxZst>,
        h5 : Step<GetIIndicesZst>,
        h6 : Step<FoldlAppsZst>,
        h7 : Step<FoldPisZst>,
    },
    #[D]
    StepDep {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        self_idx : u16,
        rec_args_hd : ExprPtr<'a>,
        rec_args_tl : ExprsPtr<'a>,
        result_tl : ExprsPtr<'a>,
        u_i_ty : ExprPtr<'a>,
        u_i_ty_red : ExprPtr<'a>,
        inner : ExprPtr<'a>,
        rec_aux_result : ExprsPtr<'a>,
        indices_result : ExprsPtr<'a>,
        valid_pos : u16,
        motive_appA : ExprPtr<'a>,
        v_i_ty : ExprPtr<'a>,
        serial : LocalSerial,
        u_app : ExprPtr<'a>,
        rec_args : ExprsPtr<'a>,
        self_idx_prime : u16,
        v_name : NamePtr<'a>,
        motive : ExprPtr<'a>,
        result_hd : ExprPtr<'a>,
        motive_appB : ExprPtr<'a>,
        #[result]
        result : ExprsPtr<'a>,
        h1 : Step<HandleRecArgsMinorZst>,
        h2 : Step<InferZst>,
        h3 : Step<WhnfZst>,
        h4 : Step<HandleRecArgsAuxZst>,
        h5 : Step<GetIIndicesZst>,
        h6 : Step<FoldlAppsZst>,
        h7 : Step<FoldlAppsZst>,
        h8 : Step<FoldPisZst>,
    }

}


#[is_step(tag="MMG", result_type = "ExprsPtr<'a>", fun = "trace_mk_minors_group")]
#[derive(Debug, Clone, Copy)]
pub enum MkMinorsGroup<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_idx : u16,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        #[result]
        minors : ExprsPtr<'a>,
    },
    #[I]
    StepIndep {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_idx : u16,
        ctor_names_hd : NamePtr<'a>,
        ctor_names_tl : NamesPtr<'a>,
        ctor_types_hd : ExprPtr<'a>,
        ctor_types_tl : ExprsPtr<'a>,
        minors_tl : ExprsPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        inner : ExprPtr<'a>,
        indices : ExprsPtr<'a>,
        valid_pos : u16,
        c_appA : ExprPtr<'a>, 
        v : ExprsPtr<'a>,
        minor_typeA : ExprPtr<'a>,  
        minor_typeB : ExprPtr<'a>,  
        minor_serial : LocalSerial,
        ctor_idx_prime : u16,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        motive : ExprPtr<'a>, 
        minor_name : NamePtr<'a>,
        minor : ExprPtr<'a>,
        #[result]
        minors : ExprsPtr<'a>,
        h1 : Step<MkMinorsGroupZst>,
        h2 : Step<SepRecCtorArgsZst>,
        h3 : Step<GetIIndicesZst>,
        h4 : Step<FoldlAppsZst>,
        h5 : Step<HandleRecArgsMinorZst>,
        h6 : Step<FoldPisZst>,
        h7 : Step<FoldPisZst>,
    },
    #[D]
    StepDep {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_idx : u16,
        ctor_names_hd : NamePtr<'a>,
        ctor_names_tl : NamesPtr<'a>,
        ctor_types_hd : ExprPtr<'a>,
        ctor_types_tl : ExprsPtr<'a>,
        minors_tl : ExprsPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        inner : ExprPtr<'a>,
        indices : ExprsPtr<'a>,
        valid_pos : u16,
        c_appA : ExprPtr<'a>, 
        v : ExprsPtr<'a>,
        minor_typeA : ExprPtr<'a>,  
        minor_typeB : ExprPtr<'a>,  
        minor_serial : LocalSerial,
        rhsB : ExprPtr<'a>,
        rhsC : ExprPtr<'a>,
        ctor_idx_prime : u16,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        motive : ExprPtr<'a>, 
        rhsA : ExprPtr<'a>,
        c_appB : ExprPtr<'a>,
        minor_name : NamePtr<'a>,
        minor : ExprPtr<'a>,
        #[result]
        minors : ExprsPtr<'a>,
        h1 : Step<MkMinorsGroupZst>,
        h2 : Step<SepRecCtorArgsZst>,
        h3 : Step<GetIIndicesZst>,
        h4 : Step<FoldlAppsZst>,
        h5 : Step<FoldlAppsZst>,
        h6 : Step<FoldlAppsZst>,
        h7 : Step<HandleRecArgsMinorZst>,
        h8 : Step<FoldPisZst>,
        h9 : Step<FoldPisZst>,
    }

}


#[is_step(tag="MMX", result_type = "ExprsPtr<'a>", fun = "trace_mk_minors_aux")]
#[derive(Debug, Clone, Copy)]
pub enum MkMinorsAux<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        ctor_types : ExprsPtr<'a>,
        #[result]
        minors : ExprsPtr<'a>,
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,

        ind_names_hd : NamePtr<'a>,
        ind_names_tl : NamesPtr<'a>,

        ind_types_hd : ExprPtr<'a>,
        ind_types_tl : ExprsPtr<'a>,
        ind_consts_hd : ExprPtr<'a>,
        ind_consts_tl : ExprsPtr<'a>,
        ctor_names_l : NamesPtr<'a>,
        ctor_names_r : NamesPtr<'a>,
        ctor_types_l : ExprsPtr<'a>,
        ctor_types_r : ExprsPtr<'a>,
        minors_l : ExprsPtr<'a>,
        minors_r : ExprsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        ctor_types : ExprsPtr<'a>,
        #[result]
        minors : ExprsPtr<'a>,
        h1 : Step<MkMinorsAuxZst>,
        h2 : Step<MkMinorsGroupZst>,
    }
}


#[is_step(tag="MMS", fun = "trace_mk_minors")]
#[derive(Debug, Clone, Copy)]
pub enum MkMinors<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        all_minors : ExprsPtr<'a>,
        h1 : Step<MkMinorsAuxZst>,
    }
}


#[is_step(tag="GRL", result_type = "LevelsPtr<'a>", fun = "trace_get_rec_levels")]
#[derive(Debug, Clone, Copy)]
pub enum GetRecLevels<'a> {
    #[P]
    Param {
        checked_indblock : CheckedIndBlockPtr,
        n : NamePtr<'a>,
        elim_level : LevelPtr<'a>,
        #[result]
        rec_levels : LevelsPtr<'a>,
        h1 : Step<MkElimLevelZst>,
    },
    #[N]
    NotParam {
        checked_indblock : CheckedIndBlockPtr,
        elim_level : LevelPtr<'a>,
        #[result]
        rec_levels : LevelsPtr<'a>,
        h1 : Step<MkElimLevelZst>,
    },

}


#[is_step(tag="RAR", result_type = "ExprsPtr<'a>", fun = "trace_handle_rec_args_rule")]
#[derive(Debug, Clone, Copy)]
pub enum HandleRecArgsRule<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        rec_args : ExprsPtr<'a>,
        #[result]
        rec_rule_parts : ExprsPtr<'a>,
    },
    #[S]
    Step {
        checked_indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        motives : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        rec_args_hd : ExprPtr<'a>,
        rec_args_tl : ExprsPtr<'a>,
        rec_rule_parts_hd : ExprPtr<'a>,
        rec_rule_parts_tl : ExprsPtr<'a>,
        u_i_ty_unred : ExprPtr<'a>,
        u_i_ty_red : ExprPtr<'a>,
        u_i_ty : ExprPtr<'a>,
        xs : ExprsPtr<'a>,
        valid_app : u16,
        indices_result : ExprsPtr<'a>,
        elim_level : LevelPtr<'a>,
        rec_levels : LevelsPtr<'a>,
        appB : ExprPtr<'a>,
        appC : ExprPtr<'a>,
        appD : ExprPtr<'a>,
        appE : ExprPtr<'a>,
        app_rhs : ExprPtr<'a>,
        rec_args : ExprsPtr<'a>,
        #[result]
        rec_rule_parts : ExprsPtr<'a>,
        rec_name : NamePtr<'a>,
        appA : ExprPtr<'a>,
        made_app : ExprPtr<'a>,
        h1 : Step<HandleRecArgsRuleZst>,
        h2 : Step<InferZst>,
        h3 : Step<WhnfZst>,
        h4 : Step<HandleRecArgsAuxZst>,
        h5 : Step<GetIIndicesZst>,
        h6 : Step<GetRecLevelsZst>,
        h7 : Step<FoldlAppsZst>,
        h8 : Step<FoldlAppsZst>,
        h9 : Step<FoldlAppsZst>,
        h10 : Step<FoldlAppsZst>,
        h11 : Step<FoldlAppsZst>,
        h12 : Step<FoldLambdasZst>,
    }

}



#[is_step(tag="MRO", result_type = "RecRulePtr<'a>", fun = "trace_mk_rec_rule1")]
#[derive(Debug, Clone, Copy)]
pub enum MkRecRule1<'a> {
    #[B]
    Base {
        checked_indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        ctor_name : NamePtr<'a>,
        ctor_type : ExprPtr<'a>,
        minors_group : ExprsPtr<'a>,
        this_minor : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        rec_args : ExprsPtr<'a>,
        inner : ExprPtr<'a>,
        rec_rule_parts : ExprsPtr<'a>,
        rhsA : ExprPtr<'a>,
        rhsB : ExprPtr<'a>,
        rhsC : ExprPtr<'a>,
        rhsD : ExprPtr<'a>,
        rhsE : ExprPtr<'a>,
        rhsF : ExprPtr<'a>,
        tel_size : u16,
        num_fields : u16,
        #[result]
        rec_rule : RecRulePtr<'a>,
        h1 : Step<SepRecCtorArgsZst>,
        h2 : Step<HandleRecArgsRuleZst>,
        h3 : Step<FoldlAppsZst>,
        h4 : Step<FoldlAppsZst>,
        h5 : Step<FoldLambdasZst>,
        h6 : Step<FoldLambdasZst>,
        h7 : Step<FoldLambdasZst>,
        h8 : Step<FoldLambdasZst>,
        h9 : Step<TelescopeSizeZst>,
    }
}


#[is_step(tag="MRG", result_type = "RecRulesPtr<'a>", fun = "trace_mk_rec_rules_group")]
#[derive(Debug, Clone, Copy)]
pub enum MkRecRulesGroup<'a> {
    #[B]
    Base {
        indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        minors_group : ExprsPtr<'a>,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        rem_minors : ExprsPtr<'a>,
        #[result]
        rec_rules : RecRulesPtr<'a>,
    },
    #[S]
    Step {
        indblock : CheckedIndBlockPtr,
        motives : ExprsPtr<'a>,
        ind_name : NamePtr<'a>,
        ind_type : ExprPtr<'a>,
        ind_const : ExprPtr<'a>,
        minors_group : ExprsPtr<'a>,
        rem_ctor_names_hd : NamePtr<'a>,
        rem_ctor_names_tl : NamesPtr<'a>,
        rem_ctor_types_hd : ExprPtr<'a>,
        rem_ctor_types_tl : ExprsPtr<'a>,
        rem_minors_hd : ExprPtr<'a>,
        rem_minors_tl : ExprsPtr<'a>,
        rec_rules_hd : RecRulePtr<'a>,
        rec_rules_tl : RecRulesPtr<'a>,
        rem_ctor_names : NamesPtr<'a>,
        rem_ctor_types : ExprsPtr<'a>,
        rem_minors : ExprsPtr<'a>,
        #[result]
        rec_rules : RecRulesPtr<'a>,
        h1 : Step<MkRecRulesGroupZst>,
        h2 : Step<MkRecRule1Zst>,
    }
}


#[is_step(tag="MRR", result_type = "RecRulesPtr<'a>", fun = "trace_mk_rec_rules")]
#[derive(Debug, Clone, Copy)]
pub enum MkRecRules<'a> {
    #[B]
    Base {
        indblock : CheckedIndBlockPtr,
        all_motives : ExprsPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        ctor_types : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        #[result]
        rec_rules : RecRulesPtr<'a>,
    },
    #[S]
    Step {
        indblock : CheckedIndBlockPtr,
        all_motives : ExprsPtr<'a>,
        
        ind_names_hd : NamePtr<'a>,
        ind_names_tl : NamesPtr<'a>,

        ind_types_hd : ExprPtr<'a>,
        ind_types_tl : ExprsPtr<'a>,

        ind_consts_hd : ExprPtr<'a>,
        ind_consts_tl : ExprsPtr<'a>,

        ctor_names_l : NamesPtr<'a>,
        ctor_names_r : NamesPtr<'a>,

        ctor_types_l : ExprsPtr<'a>,
        ctor_types_r : ExprsPtr<'a>,

        minors_l : ExprsPtr<'a>,
        minors_r : ExprsPtr<'a>,

        rec_rules_l : RecRulesPtr<'a>,
        rec_rules_r : RecRulesPtr<'a>,

        ind_names : NamesPtr<'a>,
        ind_types : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        ctor_names : NamesPtr<'a>,
        ctor_types : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        #[result]
        rec_rules : RecRulesPtr<'a>,
        h1 : Step<MkRecRulesZst>,
        h2 : Step<MkRecRulesGroupZst>,

    }
}


#[is_step(tag="MRA", result_type = "DeclarPtr<'a>", fun = "trace_mk_recursor_aux")]
#[derive(Debug, Clone, Copy)]
pub enum MkRecursorAux<'a> {
    #[I]
    BaseIndep {
        indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        num_indices : u16,
        k_target : bool,
        elim_level : LevelPtr<'a>,
        all_motives : ExprsPtr<'a>,
        motive : ExprPtr<'a>,
        major : ExprPtr<'a>,
        minors : ExprsPtr<'a>,
        rec_rules : RecRulesPtr<'a>,
        motive_app : ExprPtr<'a>,
        tyA : ExprPtr<'a>,
        tyB : ExprPtr<'a>,
        tyC : ExprPtr<'a>,
        tyD : ExprPtr<'a>,
        rec_ty : ExprPtr<'a>,
        rec_uparams : LevelsPtr<'a>,
        num_minors : u16,
        num_motives : u16,
        major_idx : u16,
        rec_name : NamePtr<'a>,
        #[result]
        recursor : DeclarPtr<'a>,
        h1 : Step<FoldlAppsZst>,
        h2 : Step<ApplyPiZst>,
        h3 : Step<FoldPisZst>,
        h4 : Step<FoldPisZst>,
        h5 : Step<FoldPisZst>,
        h6 : Step<FoldPisZst>,
        h7 : Step<GetRecLevelsZst>,
    },
    #[D]
    BaseDep {
        indblock : CheckedIndBlockPtr,
        ind_name : NamePtr<'a>,
        num_indices : u16,
        k_target : bool,
        elim_level : LevelPtr<'a>,
        all_motives : ExprsPtr<'a>,
        motive : ExprPtr<'a>,
        major : ExprPtr<'a>,
        minors : ExprsPtr<'a>,
        rec_rules : RecRulesPtr<'a>,
        motive_app_base : ExprPtr<'a>,
        tyA : ExprPtr<'a>,
        tyB : ExprPtr<'a>,
        tyC : ExprPtr<'a>,
        tyD : ExprPtr<'a>,
        rec_ty : ExprPtr<'a>,
        rec_uparams : LevelsPtr<'a>,
        num_minors : u16,
        num_motives : u16,
        major_idx : u16,
        rec_name : NamePtr<'a>,
        motive_app : ExprPtr<'a>,
        #[result]
        recursor : DeclarPtr<'a>,
        h1 : Step<FoldlAppsZst>,
        h2 : Step<ApplyPiZst>,
        h3 : Step<FoldPisZst>,
        h4 : Step<FoldPisZst>,
        h5 : Step<FoldPisZst>,
        h6 : Step<FoldPisZst>,
        h7 : Step<GetRecLevelsZst>,
    },   
}


#[is_step(tag="MR", result_type = "DeclarsPtr<'a>", fun = "trace_mk_recursors")]
#[derive(Debug, Clone, Copy)]
pub enum MkRecursors<'a> {
    #[B]
    Base {
        indblock : CheckedIndBlockPtr,
        all_motives : ExprsPtr<'a>,
        k_target : bool,
        elim_level : LevelPtr<'a>,
        ind_names : NamesPtr<'a>,
        motives : ExprsPtr<'a>,
        majors : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        rec_rules : RecRulesPtr<'a>,
        #[result]
        recursors : DeclarsPtr<'a>,
    },
    #[S]
    Step {
        indblock : CheckedIndBlockPtr,
        all_motives : ExprsPtr<'a>,
        k_target : bool,
        elim_level : LevelPtr<'a>,
        ind_names_hd : NamePtr<'a>,
        ind_names_tl : NamesPtr<'a>,
        motives_hd : ExprPtr<'a>,
        motives_tl : ExprsPtr<'a>,
        majors_hd : ExprPtr<'a>,
        majors_tl : ExprsPtr<'a>,
        minors_l : ExprsPtr<'a>,
        minors_r : ExprsPtr<'a>,
        indices_l : ExprsPtr<'a>,
        indices_r : ExprsPtr<'a>,
        rec_rules_l : RecRulesPtr<'a>,
        rec_rules_r : RecRulesPtr<'a>,
        recursors_hd : DeclarPtr<'a>,
        recursors_tl : DeclarsPtr<'a>,
        num_indices : u16,
        ind_names : NamesPtr<'a>,
        motives : ExprsPtr<'a>,
        majors : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        rec_rules : RecRulesPtr<'a>,
        #[result]
        recursors : DeclarsPtr<'a>,
        h1 : Step<MkRecursorsZst>,
        h2 : Step<MkRecursorAuxZst>,
    }

}

#[is_step(tag="CV", fun = "trace_check_vitals")]
#[derive(Debug, Clone, Copy)]
pub enum CheckVitals<'a> {
    #[B]
    Base {
        n : NamePtr<'a>,
        ups : LevelsPtr<'a>,
        t : ExprPtr<'a>,
        h1 : Step<NoDupesZst>,
        h2 : Step<InferZst>,
        h3 : Step<EnsureSortZst>,
    }
}


#[is_step(tag="GV", result_type = "DeclarView<'a>", fun = "trace_get_declar_view")]
#[derive(Debug, Clone, Copy)]
pub enum GetDeclarView<'a> {
    #[A]
    Axiom {
        #[result]
        view : DeclarView<'a>
    },
    #[D]
    Definition {
        #[result]
        view : DeclarView<'a>
    },
    #[T]
    Theorem{
        #[result]
        view : DeclarView<'a>
    },
    #[O]
    Opaque {
        #[result]
        view : DeclarView<'a>
    },
    #[Q]
    Quot {
        #[result]
        view : DeclarView<'a>
    },
    #[I]
    Inductive {
        #[result]
        view : DeclarView<'a>
    },
    #[C]
    Constructor {
        #[result]
        view : DeclarView<'a>
    },
    #[R]
    Recursor {
        #[result]
        view : DeclarView<'a>
    },
}

#[is_step(tag="AD", fun = "trace_admit_declar")]
#[derive(Debug, Clone, Copy)]
pub enum AdmitDeclar<'a> {
    // Only used for the first pass; should never be output.
    #[U]
    Unchecked {
        name : NamePtr<'a>,
    },
    #[A]
    Axiom {
        env : Option<Step<AdmitDeclarZst>>,
        n : NamePtr<'a>,
        ups : LevelsPtr<'a>,
        t : ExprPtr<'a>,
        is_unsafe : bool,
        d : DeclarPtr<'a>,
        h1 : Step<CheckVitalsZst>,
    },   
    #[D]
    SafeDef {
        env : Option<Step<AdmitDeclarZst>>,
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        hint : ReducibilityHint,
        inferred : ExprPtr<'a>,
        is_unsafe : bool,
        d : DeclarPtr<'a>,
        h1 : Step<CheckVitalsZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
    },
    #[T]
    Theorem {
        env : Option<Step<AdmitDeclarZst>>,
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        inferred : ExprPtr<'a>,
        d : DeclarPtr<'a>,
        h1 : Step<CheckVitalsZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
    },
    #[O]
    Opaque {
        env : Option<Step<AdmitDeclarZst>>,
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        is_unsafe : bool,
        inferred : ExprPtr<'a>,
        d : DeclarPtr<'a>,
        h1 : Step<CheckVitalsZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
    },
    #[Q]
    Quot {
        env : Option<Step<AdmitDeclarZst>>,
        n : NamePtr<'a>,
        ups : LevelsPtr<'a>,
        t : ExprPtr<'a>,
        d : DeclarPtr<'a>,
    },
    #[I]
    Inductives {
        env : Option<Step<AdmitDeclarZst>>,
        indblock : IndBlockPtr,
        ds : DeclarsPtr<'a>,
        params : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        ind_consts : ExprsPtr<'a>,
        codom_level : LevelPtr<'a>,
        is_zero : bool,
        is_nonzero : bool,
        checked_indblock : CheckedIndBlockPtr,
        h1 : Step<CheckIndTypesZst>,
        h2 : Step<IsZeroZst>,
        h3 : Step<IsNonzeroZst>,
        h4 : Step<MkIndTypesZst>,
    },
    #[C]
    Constructors {
        env : Option<Step<AdmitDeclarZst>>,
        indblock : CheckedIndBlockPtr,
        ctors : DeclarsPtr<'a>,
        h1 : Step<MkCtorsZst>,
    },
    #[R]
    Recursors {
        env : Step<AdmitDeclarZst>,
        checked_indblock : CheckedIndBlockPtr,
        recursors : DeclarsPtr<'a>,
        majors : ExprsPtr<'a>,
        motives : ExprsPtr<'a>,
        minors : ExprsPtr<'a>,
        indices : ExprsPtr<'a>,
        elim_level : LevelPtr<'a>,
        k_target : bool,
        rec_rules : RecRulesPtr<'a>,
        h1 : Step<MkElimLevelZst>,
        h2 : Step<InitKTargetZst>,
        h3 : Step<MkMajorsAuxZst>,
        h4 : Step<MkMotivesZst>,
        h5 : Step<MkMinorsZst>,
        h6 : Step<MkRecRulesZst>,
        h7 : Step<MkRecursorsZst>,
    }
}