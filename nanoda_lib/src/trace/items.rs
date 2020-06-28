use std::fmt::{ Display, Formatter, Result as FmtResult };
use std::fs::File;
use crate::utils::{ Ptr, List, List::*, ListPtr, IsCtx, IsLiveCtx };
use crate::name::{ NamePtr, NamesPtr, Name, StringPtr, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle, LocalSerial };
use crate::tc::eq::{ EqResult, DeltaResult };
use crate::tc::infer::InferFlag;
use crate::trace_item;
use crate::trace::IsTracer;
use crate::trace::steps::{ Step, StepIdx };
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

/*
Base implementations of `Display` so we can use the `write!` macro.
Option and Tuple need newtypes.
*/


#[derive(Debug)]
pub struct NewtypeOption<A>(pub Option<A>);


impl<A : Display> Display for NewtypeOption<A> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            NewtypeOption(None) => write!(f, "N"),
            NewtypeOption(Some(x)) => write!(f, "S{}", x),
        }
    }
}

#[derive(Debug)]
pub struct NewtypeTuple<A, B>(pub (A, B));

impl <A : Display, B : Display> Display for NewtypeTuple<A, B> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            NewtypeTuple((a, b)) => write!(f, "{}.{}", a, b)
        }
    }
}

pub trait HasPrefix : Copy {
    const PREFIX : char;
}

pub trait HasTraceItem<'a> : Sized {
    fn trace_item<CTX : IsCtx<'a>>(self, ctx : &mut CTX);
}

impl<'a> HasTraceItem<'a> for StringPtr<'a> {
    fn trace_item<CTX : IsCtx<'a>>(self, ctx : &mut CTX) {
        if (<CTX as IsCtx>::IS_PFINDER || <CTX as IsCtx>::Tracer::NOOP) {
            return
        } else {
            <CTX as IsCtx>::Tracer::trace_string(self, ctx)
        }
    }
}

impl<'a, A : HasPrefix> Display for Ptr<'a, A> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            Ptr::E(index, ..) => write!(f, "e{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::L(index, ..) => write!(f, "l{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (elem)"),
        }
    }
}

impl<'a, A : HasPrefix> Display for ListPtr<'a, A> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            Ptr::E(index, ..) => write!(f, "E{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::L(index, ..) => write!(f, "L{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (list)"),
        }
    }
}

impl<'a> Display for StringPtr<'a> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            Ptr::E(index, ..) => write!(f, "e{}s", index),
            Ptr::L(index, ..) => write!(f, "l{}s", index),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (string)"),
        }        
    }
}

impl<H> Display for Step<H> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            Step::Live { step_idx, .. } => write!(f, "{}", step_idx),
            _ => panic!("Should never request ptr_repr from a Pfind step")
        }
    }
}

impl Display for StepIdx {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Display for EqResult {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            EqResult::EqShort => write!(f, "EQ"),
            EqResult::NeShort => unreachable!("Should never try to format NeShort result!"),
        }
    }
}

impl<'a> Display for DeltaResult<'a> {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            DeltaResult::Short(r) => write!(f, "{}", r),
            DeltaResult::Exhausted(e1, e2) => write!(f, "{},{}", e1, e2),
        }
    }
}

impl Display for BinderStyle {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            BinderStyle::Default => write!(f, "d"),
            BinderStyle::Implicit => write!(f, "i"),
            BinderStyle::StrictImplicit => write!(f, "s"),
            BinderStyle::InstImplicit => write!(f, "c"),
        }
    }    
}

impl Display for LocalSerial {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

// Also special since it's non-recursive. We can just print them
// inline
impl Display for ReducibilityHint {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            ReducibilityHint::Opaq=> write!(f, "o"),
            ReducibilityHint::Reg(n) => write!(f, "{}", n),
            ReducibilityHint::Abbrev => write!(f, "a"),
        }
    }
}

impl Display for InferFlag {
    fn fmt(&self, f : &mut Formatter) -> FmtResult {
        match self {
            InferFlag::InferOnly => write!(f, "I"),
            InferFlag::Check => write!(f, "C"),
        }
    }
}


trace_item!{ 'a, Name, trace_name, trace_name_list, 'n' }
trace_item!{ 'a, Level, trace_level, trace_level_list, 'u' }
trace_item!{ 'a, Expr, trace_expr, trace_expr_list, 'e' }
trace_item!{ 'a, RecRule, trace_rec_rule, trace_rec_rule_list, 'r' }
trace_item!{ 'a, Declar, trace_declar, trace_declar_list, 'd' }

#[macro_export]
macro_rules! trace_item {
    ( $short:lifetime, $base:ident, $trace_elem:ident, $trace_list:ident, $elem_prefix:literal ) => {


        impl<$short> HasPrefix for $base<$short> {
            const PREFIX : char = $elem_prefix;
        }

        impl<$short> HasTraceItem<$short> for Ptr<$short, $base<$short>> {
            fn trace_item<CTX : IsCtx<$short>>(self, ctx : &mut CTX) {
                if (<CTX as IsCtx>::IS_PFINDER || <CTX as IsCtx>::Tracer::NOOP) {
                    return
                } else {
                    <CTX as IsCtx>::Tracer::$trace_elem(self, ctx)
                }
            }
        }
        
        impl<$short> HasTraceItem<$short> for ListPtr<$short, $base<$short>> {
            fn trace_item<CTX : IsCtx<$short>>(self, ctx : &mut CTX) {
                if (<CTX as IsCtx>::IS_PFINDER || <CTX as IsCtx>::Tracer::NOOP) {
                    return
                } else {
                    <CTX as IsCtx>::Tracer::$trace_list(self, ctx)
                }
            }
        }        
    };
}

