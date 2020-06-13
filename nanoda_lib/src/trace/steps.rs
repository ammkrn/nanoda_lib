use std::marker::PhantomData;
use crate::utils::{ Ptr, List, List::*, ListPtr, IsCtx, IsLiveCtx };
use crate::name::{ NamePtr, NamesPtr, Name, StringPtr, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle, LocalSerial };
use crate::tc::eq::ShortCircuit;
use crate::trace::IsTracer;
use crate::trace::items::{ HasPrefix, HasPtrRepr };
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

use nanoda_macros::is_step;


use Step::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StepIdx(pub usize);

impl StepIdx {
    pub fn new(n : usize) -> Self {
        StepIdx(n)
    }
}

impl std::fmt::Display for StepIdx {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            StepIdx(n) => write!(f, "{}", n)
        }
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
        evidence : PhantomData<H>,
    },
    Pfind {
        evidence : PhantomData<H>,
    },
}

impl<H> Step<H> {
    pub fn new_pfind() -> Self {
        Step::Pfind { 
            evidence : PhantomData 
        }
    }

    pub fn new_live(step_idx : StepIdx) -> Self {
        Step::Live {
            step_idx,
            evidence : PhantomData
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CalcHeight<'a> {
    placeholder : PhantomData<&'a ()>
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Find<'a> {
    placeholder : PhantomData<&'a ()>
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Infer<'l> {
    InferConst {
        arg : ExprPtr<'l>,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Whnf<'l> {
    CacheHit {
        arg : ExprPtr<'l>,
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Delta<'l> {
    placeholder : PhantomData<&'l ()>
}



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefEq<'l> {
    Refl {
        lhs : ExprPtr<'l>,
        rhs : ExprPtr<'l>,
    }
}


#[is_step(tag = "TS", result_type = "Option<usize>", fun = "trace_try_succ")]

#[derive(Debug, Clone, Copy)]
pub enum TrySucc {
    #[N]
    BaseNone {
        ind_arg1 : Option<usize>,
        #[result]
        ind_arg2 : Option<usize>
    },
    #[S]
    BaseSome {
        n : usize,
        ind_arg1 : Option<usize>,
        #[result]
        ind_arg2 : Option<usize>,
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
        h1 : Step<Mem<'a, A>>,
        ind_arg2 : ListPtr<'a, A>,
        #[result]
        ind_arg3 : bool,
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
        h1 : Step<Pos<'a, A>>,
        h2 : Step<TrySucc>,
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
        h1 : Step<Mem<'a, A>>,
        h2 : Step<IsSubset<'a, A>>,
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
        h1 : Step<Skip<'a, A>>,
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
        h1 : Step<Take<'a, A>>,
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
        h1 : Step<Mem<'a, A>>,
        h2 : Step<NoDupes<'a, A>>,
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
        h1 : Step<Get<'a, A>>,
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
        h1 : Step<Len<'a, A>>,
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
        h1 : Step<Concat<'a, A>>,
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

#[is_step(tag = "NZ", result_type = "bool", fun = "trace_is_zero_lit")]
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
        h1 : Step<Combining<'a>>,
        ind_arg1 : LevelPtr<'a>,
        ind_arg2 : LevelPtr<'a>,
        #[result]
        ind_arg3 : LevelPtr<'a>,
    },
    #[O]
    Owise {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<IsZeroLit<'a>>,
        h2 : Step<IsZeroLit<'a>>,
        h3 : Step<IsSucc<'a>>,
        h4 : Step<IsSucc<'a>>,
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
        h1 : Step<Simplify<'a>>,
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
        h1 : Step<Simplify<'a>>,
        h2 : Step<Simplify<'a>>,
        h3 : Step<Combining<'a>>,
        ind_arg1 : LevelPtr<'a>,
    },
    #[IZ]
    ImaxZero {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        h1 : Step<Simplify<'a>>,
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
        h1 : Step<Simplify<'a>>,
        h2 : Step<Simplify<'a>>,
        h3 : Step<Combining<'a>>,
        ind_arg1 : LevelPtr<'a>,
    },
    #[IO]
    ImaxOwise {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        r_prime : LevelPtr<'a>,
        h1 : Step<Simplify<'a>>,
        h2 : Step<IsZeroLit<'a>>,
        h3 : Step<IsSucc<'a>>,
        h4 : Step<Simplify<'a>>,
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
        h1 : Step<ParamsDefined<'a>>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[M]
    Max {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        h1 : Step<ParamsDefined<'a>>,
        h2 : Step<ParamsDefined<'a>>,
        ind_arg1 : LevelPtr<'a>,
        #[result]
        out : bool,
    },
    #[I]
    Imax {
        l : LevelPtr<'a>,
        r : LevelPtr<'a>,
        params : LevelsPtr<'a>,
        h1 : Step<ParamsDefined<'a>>,
        h2 : Step<ParamsDefined<'a>>,
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
        h1 : Step<ParamsDefined<'a>>,
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
        h1 : Step<SubstL<'a>>,
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
        h1 : Step<SubstL<'a>>,
        h2 : Step<SubstL<'a>>,
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
        h1 : Step<SubstL<'a>>,
        h2 : Step<SubstL<'a>>,
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
        h2 : Step<SubstL<'a>>,
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
        h1 : Step<ParamsDefinedMany<'a>>,
        h2 : Step<ParamsDefined<'a>>,
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
        ind_arg1 : LevelsPtr<'a>,
        #[result]
        ind_arg2 : LevelsPtr<'a>,
    }
}

#[is_step(tag = "EC", result_type = "bool", fun = "trace_leq_core")]
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
        h1 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
        h2 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
        h2 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
        h2 : Step<LeqCore<'a>>,
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
        h1 : Step<SubstL<'a>>,
        h2 : Step<SubstL<'a>>,
        h3 : Step<Simplify<'a>>,
        h4 : Step<Simplify<'a>>,
        h5 : Step<SubstL<'a>>,
        h6 : Step<SubstL<'a>>,
        h7 : Step<Simplify<'a>>,
        h8 : Step<Simplify<'a>>,
        h9 : Step<LeqCore<'a>>,
        h10 : Step<LeqCore<'a>>,
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
        h1 : Step<SubstL<'a>>,
        h2 : Step<SubstL<'a>>,
        h3 : Step<Simplify<'a>>,
        h4 : Step<Simplify<'a>>,
        h5 : Step<SubstL<'a>>,
        h6 : Step<SubstL<'a>>,
        h7 : Step<Simplify<'a>>,
        h8 : Step<Simplify<'a>>,
        h9 : Step<LeqCore<'a>>,
        h10 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
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
        h1 : Step<Simplify<'a>>,
        h2 : Step<LeqCore<'a>>,
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
        h1 : Step<LeqCore<'a>>,
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
        h1 : Step<Simplify<'a>>,
        h2 : Step<LeqCore<'a>>,
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
        h1 : Step<Simplify<'a>>,
        h2 : Step<Simplify<'a>>,
        h3 : Step<LeqCore<'a>>,
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
        h1 : Step<Leq<'a>>,
        h2 : Step<Leq<'a>>,
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
        h1 : Step<Leq<'a>>,
    }
}


#[is_step(tag = "IN", result_type = "bool", fun = "trace_is_nonzero")]
#[derive(Debug, Clone, Copy)]
pub enum IsNonzero<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<Leq<'a>>,
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
        h1 : Step<IsNonzero<'a>>,
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
        h1 : Step<IsZero<'a>>,
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
        h1 : Step<EqAntisymm<'a>>,
        h2 : Step<EqAntisymmMany<'a>>,
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
        h1 : Step<InstAux<'a>>,
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
    #[H]
    CacheHit {
        e : ExprPtr<'a>,
        subs : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<InstAux<'a>>,
    },
    #[V]
    VarHit {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<Get<'a, Expr<'a>>>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[M]
    VarMiss {
        dbj : u16,
        subs : ExprsPtr<'a>,
        offset : u16,
        h1 : Step<Get<'a, Expr<'a>>>,
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
        h1 : Step<InstAux<'a>>,
        h2 : Step<InstAux<'a>>,
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
        h1 : Step<InstAux<'a>>,
        h2 : Step<InstAux<'a>>,
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
        h1 : Step<InstAux<'a>>,
        h2 : Step<InstAux<'a>>,
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
        h1 : Step<InstAux<'a>>,
        h2 : Step<InstAux<'a>>,
        h3 : Step<InstAux<'a>>,
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
        h1 : Step<AbstrAux<'a>>,
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
    #[H]
    CacheHit {
        e : ExprPtr<'a>,
        locals : ExprsPtr<'a>,
        offset : u16,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<AbstrAux<'a>>,
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
        h1 : Step<Pos<'a, Expr<'a>>>,
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
        h1 : Step<Pos<'a, Expr<'a>>>,
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
        h1 : Step<AbstrAux<'a>>,
        h2 : Step<AbstrAux<'a>>,
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
        h1 : Step<AbstrAux<'a>>,
        h2 : Step<AbstrAux<'a>>,
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
        h1 : Step<AbstrAux<'a>>,
        h2 : Step<AbstrAux<'a>>,
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
        h1 : Step<AbstrAux<'a>>,
        h2 : Step<AbstrAux<'a>>,
        h3 : Step<AbstrAux<'a>>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    }    
}

#[is_step(tag="SE", result_type = "ExprPtr<'a>", fun = "trace_subst_e")]
#[derive(Debug, Clone,  Copy)]
pub enum SubstE<'a> {
    #[H]
    CacheHit {
        e : ExprPtr<'a>,
        ks : LevelsPtr<'a>,
        vs : LevelsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<SubstE<'a>>,
    },
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
        h1 : Step<SubstL<'a>>,
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
        h1 : Step<SubstLMany<'a>>,
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
        h1 : Step<SubstE<'a>>,
        h2 : Step<SubstE<'a>>,
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
        h1 : Step<SubstE<'a>>,
        h2 : Step<SubstE<'a>>,
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
        h1 : Step<SubstE<'a>>,
        h2 : Step<SubstE<'a>>,
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
        h1 : Step<SubstE<'a>>,
        h2 : Step<SubstE<'a>>,
        h3 : Step<SubstE<'a>>,
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
        h1 : Step<SubstE<'a>>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg4 : ExprPtr<'a>,
    },        
}


#[is_step(tag="IO", result_type = "bool", fun = "trace_has_ind_occ")]
#[derive(Debug, Clone,  Copy)]
pub enum HasIndOcc<'a> {
    #[H]
    CacheHit {
        e : ExprPtr<'a>,
        ind_names : NamesPtr<'a>,
        #[result]
        b : bool,
        h1 : Step<HasIndOcc<'a>>,
    },
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
        h1 : Step<Mem<'a, Name<'a>>>,
        ind_arg1 : ExprPtr<'a>,
    },
    #[A]
    App {
        fun : ExprPtr<'a>,
        arg : ExprPtr<'a>,
        ind_names : NamesPtr<'a>,
        b1 : bool,
        b2 : bool,
        h1 : Step<HasIndOcc<'a>>,
        h2 : Step<HasIndOcc<'a>>,
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
        h1 : Step<HasIndOcc<'a>>,
        h2 : Step<HasIndOcc<'a>>,
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
        h1 : Step<HasIndOcc<'a>>,
        h2 : Step<HasIndOcc<'a>>,
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
        h1 : Step<HasIndOcc<'a>>,
        h2 : Step<HasIndOcc<'a>>,
        h3 : Step<HasIndOcc<'a>>,
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
        h1 : Step<HasIndOcc<'a>>,
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
        h1 : Step<Abstr<'a>>,
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
        h1 : Step<Abstr<'a>>,
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
        h1 : Step<FoldPis<'a>>,
        h2 : Step<ApplyPi<'a>>,
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
        h1 : Step<FoldLambdas<'a>>,
        h2 : Step<ApplyLambda<'a>>,
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
        h1 : Step<FoldlApps<'a>>,
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
        h1 : Step<UnfoldAppsAux<'a>>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        out : (ExprPtr<'a>, ExprsPtr<'a>),
    },
    #[O]
    Base {
        f : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        h1 : Step<IsApp<'a>>,
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
        h1 : Step<TelescopeSize<'a>>,
        #[result]
        size : u16
    },
    #[O]
    Owise {
        e : ExprPtr<'a>,
        h1 : Step<IsPi<'a>>,
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

#[is_step(tag="WL", result_type = "ExprPtr<'a>", fun = "trace_whnf_lambda")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfLambda<'a> {
    #[X]
    NotLambda {
        e : ExprPtr<'a>,
        rem_args : ExprsPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        e_prime : ExprPtr<'a>,
        h1 : Step<IsLambda<'a>>,
        h2 : Step<Inst<'a>>,
        h3 : Step<FoldlApps<'a>>,
        #[result]
        e_prime_prime : ExprPtr<'a>

    },
    #[N]
    NoArgs {
        e : ExprPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<Inst<'a>>,
        ind_arg2 : ExprsPtr<'a>,
    },
    #[S]
    Step {
        b_name : NamePtr<'a>,
        b_type : ExprPtr<'a>,
        b_style : BinderStyle,
        body : ExprPtr<'a>,
        hd : ExprPtr<'a>,
        tl : ExprsPtr<'a>,
        lambda_args : ExprsPtr<'a>,
        #[result]
        e_prime : ExprPtr<'a>,
        h1 : Step<WhnfLambda<'a>>,
        ind_arg1 : ExprPtr<'a>,
        ind_arg2 : ExprsPtr<'a>,
    }

}


#[is_step(tag="WS", result_type = "ExprPtr<'a>", fun = "trace_whnf_sort")]
#[derive(Debug, Clone, Copy)]
pub enum WhnfSort<'a> {
    #[B]
    Base {
        l : LevelPtr<'a>,
        l_prime : LevelPtr<'a>,
        h1 : Step<Simplify<'a>>,
        ind_arg1 : ExprPtr<'a>,
        #[result]
        ind_arg2 : ExprPtr<'a>,
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
        body : ExprPtr<'a>,
        #[result]
        body_prime : ExprPtr<'a>,
        h1 : Step<Inst<'a>>,
        ind_arg1 : ExprPtr<'a>,
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
        h1 : Step<UnfoldAppsAux<'a>>,
        h2 : Step<WhnfSort<'a>>,
    },
    #[L]
    Lambda {
        e : ExprPtr<'a>,
        lam : ExprPtr<'a>,
        args : ExprsPtr<'a>,
        e_prime : ExprPtr<'a>,
        #[result]
        e_prime_prime : ExprPtr<'a>,
        h1 : Step<UnfoldAppsAux<'a>>,
        h2 : Step<WhnfLambda<'a>>,
        h3 : Step<WhnfCore<'a>>,
    },
    #[O]
    Owise {
        #[result]
        e : ExprPtr<'a>,
    }
}
