use std::io::Write;
use std::marker::PhantomData;
use nanoda_macros::is_step;
use crate::utils::{ Ptr, List, List::*, ListPtr, IsCtx, IsLiveCtx };
use crate::name::{ NamePtr, NamesPtr, Name, StringPtr, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle, LocalSerial };
use crate::tc::infer::InferFlag;
use crate::tc::eq::{ EqResult, DeltaResult }; 
use crate::trace::IsTracer;
use crate::trace::items::{ NewtypeOption, NewtypeTuple, HasPrefix };
use crate::env::{ 
    RecRulePtr, 
    RecRulesPtr, 
    RecRule, 
    Declar, 
    Declar::*, 
    DeclarPtr, 
    DeclarsPtr, 
    ReducibilityHint 
};

use Step::*;

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
    }
}

impl<H : Default> Step<H> {
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


#[is_step(tag = "LM", result_type = "bool", fun = "trace_mem")]
#[derive(Debug, Clone, Copy)]
pub enum Mem<'a, A : HasPrefix> {
    #[F]
    BaseFf {
        needle : Ptr<'a, A>,
        // [] 
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
    },
    #[T]
    BaseTt {
        needle : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
    },
    #[S]
    Step {
        needle : Ptr<'a, A>,
        x : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        bl : bool,
        h1 : Step<MemZst>,
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
    }
}

#[is_step(tag = "TS", result_type = "Option<usize>", fun = "trace_try_succ")]
#[derive(Debug, Clone, Copy)]
pub enum TrySucc {
    #[N]
    BaseNone {
        ind_arg1 : Option<usize>,
        #[result]
        ind_arg2 : Option<usize>,
    },
    #[S]
    BaseSome {
        n : usize,
        ind_arg1 : Option<usize>,
        #[result]
        ind_arg2 : Option<usize>,
    }
}

#[is_step(tag = "LP", result_type = "Option<usize>", fun = "trace_pos")]
#[derive(Debug, Clone, Copy)]
pub enum Pos<'a, A : HasPrefix> {
    #[N]
    BaseNone {
        needle : Ptr<'a, A>,
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : Option<usize>,
    },
    #[O]
    BaseSome {
        needle : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : Option<usize>,
    },
    #[S]
    Step {
        needle : Ptr<'a, A>,
        x : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        n : Option<usize>,
        #[result]
        n_prime : Option<usize>,
        h1 : Step<PosZst>,
        h2 : Step<TrySuccZst>,
        ind_arg2 : ListPtr<'a, A>,
    }
}

#[is_step(tag = "SS", result_type = "bool", fun = "trace_is_subset")]
#[derive(Debug, Clone, Copy)]
pub enum IsSubset<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        super_ : ListPtr<'a, A>,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        sub : ListPtr<'a, A>,
        super_ : ListPtr<'a, A>,
        b1 : bool,
        b2 : bool,
        h1 : Step<MemZst>,
        h2 : Step<IsSubsetZst>,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
    }
}

#[is_step(tag = "SK", result_type = "ListPtr<'a, A>", fun = "trace_skip")]
#[derive(Debug, Clone, Copy)]
pub enum Skip<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        n : usize,
        #[result]
        ind_arg1 : ListPtr<'a, A>,
    },
    #[Z]
    BaseZero {
        #[result]
        l : ListPtr<'a, A>,
        ind_arg2 : usize,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        #[result]
        l_prime : ListPtr<'a, A>,
        n_prime : usize,
        h1 : Step<SkipZst>,
        ind_arg1 : ListPtr<'a, A>,
        ind_arg2 : usize,
    }
}

#[is_step(tag = "TK", result_type = "ListPtr<'a, A>", fun = "trace_take")]
#[derive(Debug, Clone, Copy)]
pub enum Take<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        n : usize,
        #[result]
        ind_arg1 : ListPtr<'a, A>,
    },
    #[Z]
    BaseZero {
        l : ListPtr<'a, A>,
        ind_arg2 : usize,
        #[result]
        ind_arg3 : ListPtr<'a, A>,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        l_prime : ListPtr<'a, A>,
        n_prime : usize,
        h1 : Step<TakeZst>,
        ind_arg1 : ListPtr<'a, A>,
        ind_arg2 : usize,
        #[result]
        ind_arg3 : ListPtr<'a, A>,
    }
}


#[is_step(tag = "ND", result_type = "bool", fun = "trace_no_dupes")]
#[derive(Debug, Clone, Copy)]
pub enum NoDupes<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg2 : bool,
    },
    #[S]
    StepTt {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        b1 : bool,
        b2 : bool,
        h1 : Step<MemZst>,
        h2 : Step<NoDupesZst>,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg2 : bool,
    }
}



#[is_step(tag = "GT", result_type = "Option<Ptr<'a, A>>", fun = "trace_get")]
#[derive(Debug, Clone, Copy)]
pub enum Get<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        n : usize,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : Option<Ptr<'a, A>>,
    },
    #[Z]
    BaseZero {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        ind_arg1 : ListPtr<'a, A>,
        ind_arg2 : usize,
        #[result]
        ind_arg3 : Option<Ptr<'a, A>>,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        n_prime : usize,
        #[result]
        out : Option<Ptr<'a, A>>,
        h1 : Step<GetZst>,
        ind_arg1 : ListPtr<'a, A>,
        ind_arg2 : usize,
    }
}


#[is_step(tag = "LN", result_type = "usize", fun = "trace_len")]
#[derive(Debug, Clone, Copy)]
pub enum Len<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg2 : usize,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        n : usize,
        h1 : Step<LenZst>,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg2 : usize,
    }
}


#[is_step(tag = "CN", result_type = "ListPtr<'a, A>", fun = "trace_concat")]
#[derive(Debug, Clone, Copy)]
pub enum Concat<'a, A : HasPrefix> {
    #[N]
    BaseNil {
        #[result]
        l2 : ListPtr<'a, A>,
        ind_arg1 : ListPtr<'a, A>,
    },
    #[S]
    Step {
        hd : Ptr<'a, A>,
        tl : ListPtr<'a, A>,
        l2 : ListPtr<'a, A>,
        l2_prime : ListPtr<'a, A>,
        h1 : Step<ConcatZst>,
        ind_arg1 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : ListPtr<'a, A>,
    }
}

#[is_step(tag = "GP", result_type = "NamePtr<'a>", fun = "trace_get_prefix")]
#[derive(Debug, Clone, Copy)]
pub enum GetPrefix<'a> {
    #[A]
    BaseAnon {
        #[result]
        ind_arg1 : NamePtr<'a>,
    },
    #[S]
    StepStr {
        #[result]
        pfx : NamePtr<'a>,
        sfx : StringPtr<'a>,
        ind_arg1 : NamePtr<'a>,
    },
    #[N]
    StepNum {
        #[result]
        pfx : NamePtr<'a>,
        sfx : u64,
        ind_arg1 : NamePtr<'a>,
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

#[is_step(tag = "NS", result_type = "bool", fun = "trace_is_succ")]
#[derive(Debug, Clone, Copy)]
pub enum IsSucc<'a> {
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

#[is_step(tag = "AM", result_type = "bool", fun = "trace_is_any_max")]
#[derive(Debug, Clone, Copy)]
pub enum IsAnyMax<'a> {
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

#[is_step(tag = "CO", result_type = "LevelPtr<'a>", fun = "trace_combining")]
#[derive(Debug, Clone, Copy)]
pub enum Combining<'a> {
    #[L]
    Lzero {
        #[result]
        r : LevelPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
    },
    
    #[R]
    Rzero {
        #[result]
        l : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
    },
    
    #[S]
    Succ {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        x : LevelPtr<'a>,
        h1 : Step<CombiningZst>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        ind_arg3 : LevelPtr<'a>,
    },
    #[O]
    Owise {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<IsZeroLitZst>,
        h2 : Step<IsZeroLitZst>,
        h3 : Step<IsSuccZst>,
        h4 : Step<IsSuccZst>,
        #[result]
        ind_arg3 : LevelPtr<'a>,
    }
}

#[is_step(tag = "SI", result_type = "LevelPtr<'a>", fun = "trace_simplify")]
#[derive(Debug, Clone, Copy)]
pub enum Simplify<'a> {
    #[Z]
    Zero {
        #[result]
        ind_arg1 : LevelPtr<'a>,
    },
    #[P]
    Param {
        n : NamePtr<'a>,
        #[result]
        ind_arg1 : LevelPtr<'a>,
    },
    
    #[S]
    Succ {
        l : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    },
    #[M]
    Max {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        #[result]
        x : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<SimplifyZst>,
        h3 : Step<CombiningZst>,
        ind_arg1 : LevelPtr<'a>,
    },
    #[IZ]
    ImaxZero {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    },
    #[IS]
    ImaxSucc {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        #[result]
        x : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<SimplifyZst>,
        h3 : Step<CombiningZst>,
        ind_arg1 : LevelPtr<'a>,
    },
    #[IO]
    ImaxOwise {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        h1 : Step<SimplifyZst>,
        h2 : Step<IsZeroLitZst>,
        h3 : Step<IsSuccZst>,
        h4 : Step<SimplifyZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    }
}


#[is_step(tag = "PD", result_type = "bool", fun = "trace_params_defined")]
#[derive(Debug, Clone, Copy)]
pub enum ParamsDefined<'a> {
    
    #[Z]
    Zero {
        params : LevelsPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[M]
    Max {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
        h2 : Step<ParamsDefinedZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[I]
    Imax {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
        h2 : Step<ParamsDefinedZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[Q]
    BaseParam {
        n : NamePtr<'a>,
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        #[result]
        out : bool,

    },
    #[R]
    StepParam {
        n : NamePtr<'a>,
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        #[result]
        out : bool,
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
        ind_arg1 : LevelPtr<'a>,
    },
    #[S]
    Succ {
        pred : LevelPtr<'a>,
        pred_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    },
    #[M]
    Max {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    },
    #[I]
    Imax {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        ind_arg2 : LevelPtr<'a>,
    },
    #[N]
    ParamNil {
        n : NamePtr<'a>,
        #[result]
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        ind_arg3 : LevelsPtr<'a>,
    },
    #[H]
    ParamHit {
        n : NamePtr<'a>,
        #[result]
        v : LevelPtr<'a>,
        ks_tl : LevelsPtr<'a>,
        vs_tl : LevelsPtr<'a>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        ind_arg3 : LevelsPtr<'a>,
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
        h1 : bool,
        h2 : Step<SubstLZst>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        ind_arg3 : LevelsPtr<'a>,
    }
}

#[is_step(tag = "PS", result_type = "bool", fun = "trace_params_defined_many")]
#[derive(Debug, Clone, Copy)]
pub enum ParamsDefinedMany<'a> {
    #[B]
    Base {
        dec_ups : LevelsPtr<'a>,
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        out : bool,
    },
    #[S]
    Step {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        dec_ups : LevelsPtr<'a>,
        h1 : Step<ParamsDefinedManyZst>,
        h2 : Step<ParamsDefinedZst>,
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        out : bool,
    }
}


#[is_step(tag = "SM", result_type = "LevelsPtr<'a>", fun = "trace_subst_l_many")]
#[derive(Debug, Clone, Copy)]
pub enum SubstLMany<'a> {
    #[B]
    Base {
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        #[result]
        ind_arg1 : LevelsPtr<'a>,
    },
    #[S]
    Step {
        hd : LevelPtr<'a>,
        hd_prime : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        tl_prime : LevelsPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLManyZst>,
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        ind_arg2 : LevelsPtr<'a>,
    }
}

#[is_step(tag = "FI", result_type = "LevelPtr<'a>", fun = "trace_fold_imaxs")]
#[derive(Debug, Clone, Copy)]
pub enum FoldImaxs<'a> {
    #[B]
    Base {
        #[result]
        sink : LevelPtr<'a>,
        ind_arg1 : LevelsPtr<'a>,


    },
    #[S]
    Step {
        hd : LevelPtr<'a>,
        tl : LevelsPtr<'a>,
        r : LevelPtr<'a>,
        #[result]
        out : LevelPtr<'a>,
        ind_arg1 : LevelsPtr<'a>,
        h1 : Step<FoldImaxsZst>,
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
        h1 : bool,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[AZ]
    AnyZ {
        l : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        h1 : bool,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[PP]
    ParamParam {
        n1 : NamePtr<'a>,
        n2 : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[PZ]
    ParamZero {
        n : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool,
    },
    #[ZP]
    ZeroParam {
        n : NamePtr<'a>,
        l_h : usize,
        r_h : usize,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool,

    },
    #[SA]
    SuccAny {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        b : bool,
        h1 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
    },
    #[AS]
    AnySucc {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        b : bool,
        h1 : Step<LeqCoreZst>,
        ind_arg2 : LevelPtr<'a>,
    },
    #[MA]
    MaxAny {
        a : LevelPtr<'a>,
        b : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        b1 : bool,
        b2 : bool,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[PM]
    ParamMax {
        n : NamePtr<'a>,
        x : LevelPtr<'a>,
        y : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        l_h : usize,
        r_h : usize,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool

    },
    #[ZM]
    ZeroMax {
        x : LevelPtr<'a>,
        y : LevelPtr<'a>,
        b1 : bool,
        b2 : bool,
        l_h : usize,
        r_h : usize,
        h1 : Step<LeqCoreZst>,
        h2 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[IC]
    ImaxCongr {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[IL]
    ImaxParamL {
        n : NamePtr<'a>,
        a : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_z : LevelPtr<'a>,
        r_z : LevelPtr<'a>,
        l_z_prime : LevelPtr<'a>,
        r_z_prime : LevelPtr<'a>,
        l_succ : LevelPtr<'a>,
        r_succ : LevelPtr<'a>,
        l_succ_prime : LevelPtr<'a>,
        r_succ_prime : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        b1 : bool,
        b2 : bool,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
        h3 : Step<SimplifyZst>,
        h4 : Step<SimplifyZst>,
        h5 : Step<SubstLZst>,
        h6 : Step<SubstLZst>,
        h7 : Step<SimplifyZst>,
        h8 : Step<SimplifyZst>,
        h9 : Step<LeqCoreZst>,
        h10 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[IR]
    ImaxParamR {
        n : NamePtr<'a>,
        x : LevelPtr<'a>,
        l : LevelPtr<'a>,
        l_z : LevelPtr<'a>,
        r_z : LevelPtr<'a>,
        l_z_prime : LevelPtr<'a>,
        r_z_prime : LevelPtr<'a>,
        l_succ : LevelPtr<'a>,
        r_succ : LevelPtr<'a>,
        l_succ_prime : LevelPtr<'a>,
        r_succ_prime : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        b1 : bool,
        b2 : bool,
        h1 : Step<SubstLZst>,
        h2 : Step<SubstLZst>,
        h3 : Step<SimplifyZst>,
        h4 : Step<SimplifyZst>,
        h5 : Step<SubstLZst>,
        h6 : Step<SubstLZst>,
        h7 : Step<SimplifyZst>,
        h8 : Step<SimplifyZst>,
        h9 : Step<LeqCoreZst>,
        h10 : Step<LeqCoreZst>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        res : bool
    },
    #[LI] 
    ImaxImaxAny {
        a : LevelPtr<'a>,
        c : LevelPtr<'a>,
        d : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_h : usize,
        r_h : usize,
        #[result]
        b : bool,
        h1 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
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
        b : bool,
        h1 : Step<SimplifyZst>,
        h2 : Step<LeqCoreZst>,
        ind_arg1 : LevelPtr<'a>,
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
        b : bool,
        h1 : Step<LeqCoreZst>,
        ind_arg2 : LevelPtr<'a>,

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
        b : bool,
        h1 : Step<SimplifyZst>,
        h2 : Step<LeqCoreZst>,
        ind_arg2 : LevelPtr<'a>,
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
        h1 : Step<LeqZst>,
        h2 : Step<LeqZst>,
        #[result]
        ind_arg3 : bool,
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
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        b : bool,
    },
    #[L]
    BaseFL {
        l : LevelPtr<'a>,
        ls : LevelsPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        #[result]
        b : bool
    },
    #[R]
    BaseFR {
        r : LevelPtr<'a>,
        rs : LevelsPtr<'a>,
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        b : bool
    },
    #[S]
    Step {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        ls : LevelsPtr<'a>,
        rs : LevelsPtr<'a>,
        b1 : bool,
        b2 : bool,
        h1 : Step<EqAntisymmZst>,
        h2 : Step<EqAntisymmManyZst>,
        ind_arg1 : LevelsPtr<'a>,
        ind_arg2 : LevelsPtr<'a>,
        #[result]
        b : bool,
    }
}

/*
#[is_step(tag = "VB", result_type = "usize", fun = "trace_var_bound")]
#[derive(Debug, Clone, Copy)]
pub enum VarBound<'a> {
    #[V]
    Var {

    },
    #[S]
    Sort {

    },
    #[C]
    Const {

    },
    #[A]
    App {

    },
    #[P]
    Pi {

    },
    #[L]
    Lambda {

    },
    #[Z]
    Let {

    },
    #[X]
    Local {

    }
}
*/


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
        h1 : bool,
    },
    #[V]
    VarHit {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<GetZst>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[M]
    VarMiss {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        h1 : Step<GetZst>,
        #[result]
        ind_arg1 : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>
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
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<InstAuxZst>,
        h2 : Step<InstAuxZst>,
        h3 : Step<InstAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<AbstrAuxZst>,
        #[result]
        ind_arg3 : ExprPtr<'a>,
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
        h1 : Step<PosZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },
    #[M]
    LocalMiss {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        locals : ExprsPtr<'a>,
        offset : u16,
        h1 : Step<PosZst>,
        #[result]
        ind_arg1 : ExprPtr<'a>
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        offset : u16,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        body_prime : ExprPtr<'a>,
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<AbstrAuxZst>,
        h2 : Step<AbstrAuxZst>,
        h3 : Step<AbstrAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        ind_arg1 : ExprPtr<'a>,
    },
    #[S]
    Sort {
        l : LevelPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        l_prime : LevelPtr<'a>,
        h1 : Step<SubstLZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        levels_prime : LevelsPtr<'a>,
        h1 : Step<SubstLManyZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        fun_prime : ExprPtr<'a>,
        arg_prime : ExprPtr<'a>,
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<SubstEZst>,
        h2 : Step<SubstEZst>,
        h3 : Step<SubstEZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },        
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        b_type_prime : ExprPtr<'a>,
        serial_prime : LocalSerial,
        h1 : Step<SubstEZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },        
}

#[is_step(tag="CH", result_type = "u16", fun = "trace_calc_height_aux")]
#[derive(Debug, Clone,  Copy)]
pub enum CalcHeightAux<'a> {
    #[V]
    Var {
        dbj : u16,
        #[result]
        height : u16,
        ind_arg1 : ExprPtr<'a>,
    },
    #[S]
    Sort {
        level : LevelPtr<'a>,
        #[result]
        height : u16,
        ind_arg1 : ExprPtr<'a>,
    },
    #[H]
    ConstHit {
        n : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        d_uparams : LevelsPtr<'a>,
        d_type : ExprPtr<'a>,
        d_val : ExprPtr<'a>,
        d_hint : ReducibilityHint,
        d_is_unsafe : bool,
        #[result]
        height : u16,
        h1 : Step<AdmitDeclarZst>,
        ind_arg1 : ExprPtr<'a>,

    },
    #[M]
    ConstMiss {
        n : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        #[result]
        height : u16,
        ind_arg1 : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[P]
    Pi {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle, 
        b : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[L]
    Lambda {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle, 
        b : ExprPtr<'a>,
        height1 : u16,
        height2 : u16,
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
        ind_arg1 : ExprPtr<'a>,
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
        #[result]
        height : u16,
        h1 : Step<CalcHeightAuxZst>,
        h2 : Step<CalcHeightAuxZst>,
        h3 : Step<CalcHeightAuxZst>,
        ind_arg1 : ExprPtr<'a>,
    },
}


#[is_step(tag="IO", result_type = "bool", fun = "trace_has_ind_occ")]
#[derive(Debug, Clone,  Copy)]
pub enum HasIndOcc<'a> {
    #[V]
    Var {
        dbj : u16,
        ind_names : NamesPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool,
    },
    #[S]
    Sort {
        l : LevelPtr<'a>,
        ind_names : NamesPtr<'a>,
        ind_arg1  : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool,
    },
    #[C]
    Const {
        name : NamePtr<'a>,
        levels : LevelsPtr<'a>,
        ind_names : NamesPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<MemZst>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_names : NamesPtr<'a>,
        b1 : bool,
        b2 : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool,
    },
    #[P]
    Pi {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b1 : bool,
        b2 : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool
    },
    #[L]
    Lambda {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        b1 : bool,
        b2 : bool,
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool
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
        h1 : Step<HasIndOccZst>,
        h2 : Step<HasIndOccZst>,
        h3 : Step<HasIndOccZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool
    },
    #[X]
    Local {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        serial : LocalSerial,
        h1 : Step<HasIndOccZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg3 : bool
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
        h1 : Step<AbstrZst>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
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
        h1 : Step<AbstrZst>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    }
}

#[is_step(tag="FP", result_type = "ExprPtr<'a>", fun = "trace_fold_pis")]
#[derive(Debug, Clone,  Copy)]
pub enum FoldPis<'a> {
    #[N]
    Nil {
        ind_arg1 : ExprsPtr<'a>,
        #[result]
        body : ExprPtr<'a>,
    },
    #[C]
    Cons {
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        body : ExprPtr<'a>,
        sink : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<FoldPisZst>,
        h2 : Step<ApplyPiZst>,
        ind_arg1 : ExprsPtr<'a>,
    }
}

#[is_step(tag="FL", result_type = "ExprPtr<'a>", fun = "trace_fold_lambdas")]
#[derive(Debug, Clone,  Copy)]
pub enum FoldLambdas<'a> {
    #[N]
    Nil {
        ind_arg1 : ExprsPtr<'a>,
        #[result]
        body : ExprPtr<'a>,
    },
    #[C]
    Cons {
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        body : ExprPtr<'a>,
        sink : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<FoldLambdasZst>,
        h2 : Step<ApplyLambdaZst>,
        ind_arg1 : ExprsPtr<'a>,
    }
}

#[is_step(tag="FA", result_type = "ExprPtr<'a>", fun = "trace_foldl_apps")]
#[derive(Debug, Clone, Copy)]
pub enum FoldlApps<'a> {
    #[N]
    Nil {
        #[result]
        base : ExprPtr<'a>,
        ind_arg1 : ExprsPtr<'a>,
    },
    #[C]
    Cons {
        base : ExprPtr<'a>,
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        #[result]
        folded : ExprPtr<'a>,
        h1 : Step<FoldlAppsZst>,
        ind_arg2 : ExprsPtr<'a>

    }
}

#[is_step(tag="UX", result_type = "(ExprPtr<'a>, ExprsPtr<'a>)", fun = "trace_unfold_apps_aux")]
#[derive(Debug, Clone, Copy)]
pub enum UnfoldAppsAux<'a> {
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        sink : ExprsPtr<'a>,
        base_f : ExprPtr<'a>,
        all_args : ExprsPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        out : (ExprPtr<'a>, ExprsPtr<'a>),
    },
    #[O]
    Base {
        f : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        h1 : Step<IsAppZst>,
        #[result]
        out : (ExprPtr<'a>, ExprsPtr<'a>),
    }
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
        inner_size : u16,
        h1 : Step<TelescopeSizeZst>,
        #[result]
        size : u16
    },
    #[O]
    Owise {
        e : ExprPtr<'a>,
        h1 : Step<IsPiZst>,
        #[result]
        size : u16
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
        h1 : Step<SimplifyZst>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : ExprPtr<'a>,
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
        h1 : Step<InstZst>,
        h2 : Step<WhnfCoreZst>,
        ind_arg2 : ExprsPtr<'a>,
    },
    #[S]
    Step {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        arg_hd : ExprPtr<'a>,
        args_tl : ExprsPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        #[result]
        b_prime : ExprPtr<'a>,
        h1 : Step<WhnfLambdaZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
    }

}



#[is_step(tag="WZ", result_type = "ExprPtr<'a>", fun = "trace_whnf_let")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfLet<'a> {
    #[B]
    Base {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        val : ExprPtr<'a>,
        body_A : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        body_B : ExprPtr<'a>,
        body_C : ExprPtr<'a>,
        #[result]
        body_D : ExprPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<FoldlAppsZst>,
        h3 : Step<WhnfCoreZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}


#[is_step(tag="QL", result_type = "ExprPtr<'a>", fun = "trace_reduce_quot_lift")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceQuotLift<'a> {
    #[B]
    Base {
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        qmk_A_r_a_unred : ExprPtr<'a>,
        qmk_A_r : ExprPtr<'a>,
        a : ExprPtr<'a>,
        qmk_levels : LevelsPtr<'a>,
        qmk_args : ExprsPtr<'a>,
        f : ExprPtr<'a>,
        skipped : ExprsPtr<'a>,
        out_unred : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<GetZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<UnfoldAppsAuxZst>,
        h4 : Step<GetZst>,
        h5 : Step<SkipZst>,
        h6 : Step<FoldlAppsZst>,
        h7 : Step<WhnfCoreZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}

#[is_step(tag="QI", result_type = "ExprPtr<'a>", fun = "trace_reduce_quot_ind")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceQuotInd<'a> {
    #[B]
    Base {
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        qmk_A_r_a_unred : ExprPtr<'a>,
        qmk_A_r : ExprPtr<'a>,
        a : ExprPtr<'a>,
        qmk_levels : LevelsPtr<'a>,
        qmk_args : ExprsPtr<'a>,
        B_of : ExprPtr<'a>,
        skipped : ExprsPtr<'a>,
        out_unred : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<GetZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<UnfoldAppsAuxZst>,
        h4 : Step<GetZst>,
        h5 : Step<SkipZst>,
        h6 : Step<FoldlAppsZst>,
        h7 : Step<WhnfCoreZst>,
        ind_arg1 : ExprPtr<'a>,
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
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<AdmitDeclarZst>,
        h3 : Step<GetZst>,
        h4 : Step<TakeZst>,
        h5 : Step<FoldlAppsZst>,
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
    ByAux {
        major : ExprPtr<'a>,
        major_name : NamePtr<'a>,
        major_levels : LevelsPtr<'a>,
        major_args : ExprsPtr<'a>,
        rrs : RecRulesPtr<'a>,
        #[result]
        rule : RecRulePtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<GetRecRuleAuxZst>,
    }
}

#[is_step(tag="RX", result_type = "RecRulePtr<'a>", fun = "trace_get_rec_rule_aux")]
#[derive(Debug, Clone, Copy)]
pub enum GetRecRuleAux<'a> {
    #[B]
    Base {
        major_name : NamePtr<'a>,
        num_fields : u16,
        val : ExprPtr<'a>,
        tl : RecRulesPtr<'a>,
        ind_arg1 : RecRulesPtr<'a>,
        #[result]
        ind_arg3 : RecRulePtr<'a>,
    },
    #[S]
    Step {
        ctor_name : NamePtr<'a>,
        num_fields : u16,
        val : ExprPtr<'a>,
        major_name : NamePtr<'a>,
        rest : RecRulesPtr<'a>,
        #[result]
        out_rule : RecRulePtr<'a>,
        h1 : Step<GetRecRuleAuxZst>,
        ind_arg1 : RecRulesPtr<'a>,
    }
}


#[is_step(tag="RI", result_type = "ExprPtr<'a>", fun = "trace_reduce_ind_rec")]
#[derive(Debug, Clone, Copy)]
pub enum ReduceIndRec<'a> {
    #[B]
    Base {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
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
        rr_name : NamePtr<'a>,
        rr_n_fields : u16,
        rr_val : ExprPtr<'a>,
        major_unredA : ExprPtr<'a>,
        major_unredB : ExprPtr<'a>,
        major : ExprPtr<'a>,
        major_fun : ExprPtr<'a>,
        major_args : ExprsPtr<'a>,
        rec_rule : RecRulePtr<'a>,
        major_args_len : usize,
        skip1 : ExprsPtr<'a>,
        take1 : ExprsPtr<'a>,
        skip2 : ExprsPtr<'a>,
        take2 : ExprsPtr<'a>,
        r12 : ExprPtr<'a>,
        r13 : ExprPtr<'a>,
        r14 : ExprPtr<'a>,
        r15 : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<AdmitDeclarZst>,
        h2 : Step<GetZst>,
        h3 : Step<ToCtorWhenKZst>,
        h4 : Step<WhnfZst>,
        h5 : Step<UnfoldAppsAuxZst>,
        h6 : Step<GetRecRuleZst>,
        h7 : Step<LenZst>,
        h8 : Step<SkipZst>,
        h9 : Step<TakeZst>,
        h10 : Step<SkipZst>,
        h11 : Step<TakeZst>,
        h12 : Step<SubstEZst>,
        h13 : Step<FoldlAppsZst>,
        h14 : Step<FoldlAppsZst>,
        h15 : Step<FoldlAppsZst>,
        h16 : Step<WhnfCoreZst>,
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
        eA : ExprPtr<'a>,
        eB : ExprPtr<'a>,
        eC : ExprPtr<'a>,
        #[result]
        eD : ExprPtr<'a>,
        h1 : Step<WhnfCoreZst>,
        h2 : Step<UnfoldDefZst>,
        h3 : Step<WhnfZst>,
    }
}


#[is_step(tag="ID", result_type = "DeclarPtr<'a>", fun = "trace_is_delta")]
#[derive(Debug, Clone, Copy)]
pub enum IsDelta<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        args : ExprsPtr<'a>,
        // def info
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        hint : ReducibilityHint,
        is_unsafe : bool,
        //
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<AdmitDeclarZst>,
        #[result]
        ind_arg2 : DeclarPtr<'a>
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
        d_hint : ReducibilityHint,
        d_is_unsafe : bool,
        uparams_len : usize,
        d_val_prime : ExprPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAuxZst>,
        h2 : Step<AdmitDeclarZst>,
        h3 : Step<LenZst>,
        h4 : Step<LenZst>,
        h5 : Step<SubstEZst>,
        h6 : Step<FoldlAppsZst>,
    },
}

#[is_step(tag="SZ", fun = "trace_is_sort_zero")]
#[derive(Debug, Clone, Copy)]
pub enum IsSortZero<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
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
    #[SN]
    SomeNone {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_def : DeclarPtr<'a>,
        l_defval_unred : ExprPtr<'a>,
        l_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<UnfoldDefZst>,
        h3 : Step<WhnfCoreZst>,
        h4 : Step<LazyDeltaStepZst>,
    },
    #[NS]
    NoneSome {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        r_def : DeclarPtr<'a>,
        r_defval_unred : ExprPtr<'a>,
        r_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<UnfoldDefZst>,
        h3 : Step<WhnfCoreZst>,
        h4 : Step<LazyDeltaStepZst>,
    },
    #[LT]
    Lt {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_def : DeclarPtr<'a>,
        r_def : DeclarPtr<'a>,
        l_hint : ReducibilityHint,
        r_hint : ReducibilityHint,
        r_defval_unred : ExprPtr<'a>,
        r_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<IsDeltaZst>,
        h3 : Step<UnfoldDefZst>,
        h4 : Step<WhnfCoreZst>,
        h5 : Step<LazyDeltaStepZst>,
    },
    #[GT]
    Gt {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_def : DeclarPtr<'a>,
        r_def : DeclarPtr<'a>,
        l_hint : ReducibilityHint,
        r_hint : ReducibilityHint,
        l_defval_unred : ExprPtr<'a>,
        l_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<IsDeltaZst>,
        h3 : Step<UnfoldDefZst>,
        h4 : Step<WhnfCoreZst>,
        h5 : Step<LazyDeltaStepZst>,
    },
    #[E]
    Extensional {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_def : DeclarPtr<'a>,
        r_def : DeclarPtr<'a>,
        lc_name : NamePtr<'a>,
        rc_name : NamePtr<'a>,
        lc_levels : LevelsPtr<'a>,
        rc_levels : LevelsPtr<'a>,
        l_args : ExprsPtr<'a>,
        r_args : ExprsPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<IsDeltaZst>,
        h3 : Step<UnfoldAppsAuxZst>,
        h4 : Step<UnfoldAppsAuxZst>,
        h5 : Step<ArgsEqZst>,
        h6 : Step<EqAntisymmManyZst>,
    },
    #[O]
    Owise {
        l : ExprPtr<'a>,
        r : ExprPtr<'a>,
        l_def : DeclarPtr<'a>,
        r_def : DeclarPtr<'a>,
        l_defval_unred : ExprPtr<'a>,
        r_defval_unred : ExprPtr<'a>,
        l_defval : ExprPtr<'a>,
        r_defval : ExprPtr<'a>,
        #[result]
        result : DeltaResult<'a>,
        h1 : Step<IsDeltaZst>,
        h2 : Step<IsDeltaZst>,
        h3 : Step<UnfoldDefZst>,
        h4 : Step<UnfoldDefZst>,
        h5 : Step<WhnfCoreZst>,
        h6 : Step<WhnfCoreZst>,
        h7 : Step<LazyDeltaStepZst>,
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
        #[result]
        result : EqResult,
        h1 : Step<EqAntisymmZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprPtr<'a>,
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
        doms : ExprsPtr<'a>,
        lt_prime : ExprPtr<'a>,
        rt_prime : ExprPtr<'a>,
        local : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<DefEqLambdaZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprPtr<'a>,
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
        doms : ExprsPtr<'a>,
        lt_prime : ExprPtr<'a>,
        rt_prime : ExprPtr<'a>,
        local : ExprPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<InstZst>,
        h2 : Step<InstZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<DefEqPiZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprPtr<'a>,
    }    
}


#[is_step(tag="AF", result_type = "EqResult", fun = "trace_args_eq")]
#[derive(Debug, Clone, Copy)]
pub enum ArgsEq<'a> {
    #[B]
    Base {
        ls : ExprsPtr<'a>,
        rs : ExprsPtr<'a>,
        ls_len : usize,
        rs_len : usize,
        #[result]
        result : EqResult,
        h1 : Step<LenZst>,
        h2 : Step<LenZst>,
        h3 : Step<ArgsEqAuxZst>,
    },
}
#[is_step(tag="FX", result_type = "EqResult", fun = "trace_args_eq_aux")]
#[derive(Debug, Clone, Copy)]
pub enum ArgsEqAux<'a> {
    #[R]
    Refl {
        ind_arg1 : ExprsPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
        #[result]
        result : EqResult,
    },
    #[B]
    Base {
        ind_arg1 : ExprsPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
        #[result]
        result : EqResult,
    },
    #[S]
    Step {
        x  : ExprPtr<'a>,
        y  : ExprPtr<'a>,
        xs : ExprsPtr<'a>,
        ys : ExprsPtr<'a>,
        #[result]
        result : EqResult,
        h1 : Step<DefEqZst>,
        h2 : Step<ArgsEqAuxZst>,
        ind_arg1 : ExprsPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
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
        #[result]
        result : EqResult,
        h1 : Step<EqAntisymmManyZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprPtr<'a>,
    }
}


#[is_step(tag="EX", result_type = "EqResult", fun = "trace_def_eq_local")]
#[derive(Debug, Clone, Copy)]
pub enum DefEqLocal<'a> {
    #[B]
    Base {
        ln : NamePtr<'a>,
        rn : NamePtr<'a>,
        ls : BinderStyle,
        rs : BinderStyle,
        lt : ExprPtr<'a>,
        rt : ExprPtr<'a>,
        #[result]
        result : EqResult,
        l_serial : LocalSerial,
        r_serial : LocalSerial,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprPtr<'a>,
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
        h4 : Step<ArgsEqZst>,
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
        #[result]
        result : EqResult,
        h1 : Step<InferZst>,
        h2 : Step<WhnfZst>,
        h3 : Step<DefEqZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}





#[is_step(tag="ENS", result_type = "LevelPtr<'a>", fun = "trace_ensure_sort")]
#[derive(Debug, Clone, Copy)]
pub enum EnsureSort<'a> {
    #[B]
    Base {
        #[result]
        level : LevelPtr<'a>,
        ind_arg1 : ExprPtr<'a>,

    },
    #[R]
    Reduce {
        e : ExprPtr<'a>,
        #[result]
        level : LevelPtr<'a>,
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
        #[result]
        inferred : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[C]
    Checked {
        l : LevelPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<ParamsDefinedZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}

#[is_step(tag="IC", result_type = "ExprPtr<'a>", fun = "trace_infer_const")]
#[derive(Debug, Clone, Copy)]
pub enum InferConst<'a> {
    #[I]
    InferOnly {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        flag : InferFlag,
        dec : DeclarPtr<'a>,
        dec_uparams : LevelsPtr<'a>,
        dec_type : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        h1 : Step<AdmitDeclarZst>,
        h2 : Step<SubstEZst>,
    },
    #[C]
    Checked {
        c_name : NamePtr<'a>,
        c_levels : LevelsPtr<'a>,
        flag : InferFlag,
        dec : DeclarPtr<'a>,
        dec_uparams : LevelsPtr<'a>,
        dec_type : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        ind_arg1 : ExprPtr<'a>,
        h1 : Step<AdmitDeclarZst>,
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
        args : ExprsPtr<'a>,
        context : ExprsPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InferAppZst>,
        ind_arg1 : ExprPtr<'a>,
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
        h1 : Step<InstZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<InferAppZst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
    },
    #[SN]
    StepNotPi {
        e_type : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        context : ExprsPtr<'a>,
        flag : InferFlag,
        e_type_prime : ExprPtr<'a>,
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
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
        e_type : ExprPtr<'a>,
        #[result]
        level : LevelPtr<'a>,
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
        b_type_prime : ExprPtr<'a>,
        inferred_level : LevelPtr<'a>,
        local : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<InferSortOfZst>,
        h3 : Step<InferPiZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}


#[is_step(tag="FO", result_type = "ExprPtr<'a>", fun = "trace_fold_pis_once")]
#[derive(Debug, Clone, Copy)]
pub enum FoldPisOnce<'a> {
    #[B]
    Base {
        #[result]
        out : ExprPtr<'a>,
        ind_arg1 : ExprsPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
    },
    #[S]
    Step {
        t : ExprPtr<'a>,
        n : NamePtr<'a>,
        unused_t : ExprPtr<'a>,
        s : BinderStyle,
        ts : ExprsPtr<'a>,
        ls : ExprsPtr<'a>,
        body : ExprPtr<'a>,
        combined : ExprPtr<'a>,
        #[result]
        out : ExprPtr<'a>,
        h1 : Step<FoldPisOnceZst>,
        ind_arg1 : ExprsPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
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
        flag : InferFlag,
        b_type_prime : ExprPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
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
        flag : InferFlag,
        b_type_prime : ExprPtr<'a>,
        b_type_sort : LevelPtr<'a>,
        #[result]
        inferred : ExprPtr<'a>,
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
        h1 : Step<InstZst>,
        h2 : Step<InferZst>,
        ind_arg1 : ExprPtr<'a>,
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
        h1 : Step<InferSortOfZst>,
        h2 : Step<InferZst>,
        h3 : Step<DefEqZst>,
        h4 : Step<InstZst>,
        h5 : Step<InferZst>,
        ind_arg1 : ExprPtr<'a>,
    }
}


#[is_step(tag="IX", result_type = "ExprPtr<'a>", fun = "trace_infer_local")]
#[derive(Debug, Clone, Copy)]
pub enum InferLocal<'a> {
    #[B]
    Base {
        b_name : NamePtr<'a>,
        #[result]
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        ind_arg1 : ExprPtr<'a>,
    }
}


#[is_step(tag="LPS", result_type = "ExprsPtr<'a>", fun = "trace_mk_local_params")]
#[derive(Debug, Clone, Copy)]
pub enum MkLocalParams<'a> {
    #[B]
    Base {
        rem_params : u16,
        ind_type : ExprPtr<'a>,
        #[result]
        ind_arg3 : ExprsPtr<'a>,
    },
    #[S]
    Step {
        rem_params : u16,
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        #[result]
        sink : ExprsPtr<'a>,
        h1 : Step<InstZst>,
        h2 : Step<MkLocalParamsZst>,
        ind_arg2 : ExprPtr<'a>,
        ind_arg3 : ExprsPtr<'a>,
    }


    
}

#[is_step(tag="LIT", result_type = "ExprsPtr<'a>", fun = "trace_mk_local_indices1")]
#[derive(Debug, Clone, Copy)]
pub enum MkLocalIndices1<'a> {
    #[B]
    Base {
        e : ExprPtr<'a>,
        h1 : Step<IsPiZst>, 
        ind_arg2 : ExprsPtr<'a>,
        #[result]
        ind_arg3 : ExprsPtr<'a>,
    },
    #[I]
    StepIndex {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        serial : LocalSerial,
        b_prime : ExprPtr<'a>,
        local_indices : ExprsPtr<'a>,
        h1 : Step<InstZst>, 
        h2 : Step<MkLocalIndices1Zst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
        #[result]
        ind_arg3 : ExprsPtr<'a>,
    },
    #[P]
    StepParam {
        n : NamePtr<'a>,
        t : ExprPtr<'a>,
        s : BinderStyle,
        b : ExprPtr<'a>,
        b_prime : ExprPtr<'a>,
        local_param : ExprPtr<'a>,
        local_params : ExprsPtr<'a>,
        #[result]
        local_indices : ExprsPtr<'a>,
        h1 : Step<InstZst>, 
        h2 : Step<MkLocalIndices1Zst>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
    }
}


#[is_step(tag="LIS", result_type = "ExprsPtr<'a>", fun = "trace_mk_local_indices_aux")]
#[derive(Debug, Clone, Copy)]
pub enum MkLocalIndicesAux<'a> {
    #[B]
    Base {
        #[result]
        sink : ExprsPtr<'a>,
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


#[is_step(tag="AD", result_type = "NamePtr<'a>", fun = "trace_admit_declar")]
#[derive(Debug, Clone, Copy)]
pub enum AdmitDeclar<'a> {
    #[AX]
    Axiom {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        is_unsafe : bool,
    },
    #[DE]
    Definition {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        hint : ReducibilityHint,
        is_unsafe : bool,
    },
    #[TH]
    Theorem {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    #[OP]
    Opaque {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    #[QU]
    Quot {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
    },
    #[IN]
    Inductive {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        num_params : u16,
        all_ind_names : NamesPtr<'a>,
        all_ctor_names : NamesPtr<'a>,
        is_unsafe : bool,
    },
    #[CT]
    Constructor {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        parent_name : NamePtr<'a>,
        num_fields : u16,
        minor_idx : u16,
        num_params : u16,
        is_unsafe : bool,   
    },
    #[RE]
    Recursor {
        #[result]
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        all_names : NamesPtr<'a>,
        num_params : u16,
        num_indices : u16,
        num_motives : u16,
        num_minors : u16,
        major_idx : u16,
        rec_rules : ListPtr<'a, RecRule<'a>>,
        is_k : bool,
        is_unsafe : bool,
    }
}