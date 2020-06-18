use std::fs::File;
use crate::utils::{ Ptr, List, List::*, ListPtr, IsCtx, IsLiveCtx };
use crate::name::{ NamePtr, NamesPtr, Name, StringPtr, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle, LocalSerial };
use crate::tc::eq::{ DeltaResult, ShortCircuit };
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


pub trait HasPrefix : Copy {
    const PREFIX : char;
    const LIST_PREFIX : char;
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

pub trait HasPtrRepr {
    fn ptr_repr(self) -> String;
}

// All integer types are just printed as integer literals.
impl HasPtrRepr for usize {
    fn ptr_repr(self) -> String {
        self.to_string()
    }
}

impl HasPtrRepr for u16 {
    fn ptr_repr(self) -> String {
        self.to_string()
    }
}

impl HasPtrRepr for u64 {
    fn ptr_repr(self) -> String {
        self.to_string()
    }
}

impl HasPtrRepr for bool {
    fn ptr_repr(self) -> String {
        match self {
            true => format!("t"),
            false => format!("f")
        }
    }
}

impl HasPtrRepr for ShortCircuit {
    fn ptr_repr(self) -> String {
        match self {
            ShortCircuit::EqShort => format!("eq"),
            ShortCircuit::NeqShort => format!("ne"),
        }
    }
}


impl<'a> HasPtrRepr for DeltaResult<'a> {
    fn ptr_repr(self) -> String {
        match self {
            DeltaResult::Short(s) => s.ptr_repr(),
            DeltaResult::Exhausted(e1, e2) => (e1, e2).ptr_repr(),
        }
    }
}

impl<A, B> HasPtrRepr for (A, B)
where A : HasPtrRepr,
      B : HasPtrRepr {
    fn ptr_repr(self) -> String {
        format!("({},{})", self.0.ptr_repr(), self.1.ptr_repr())
    }
}


// There's only one 3-tuple used, it's in inductive.
impl<A, B, C> HasPtrRepr for (A, B, C)
where A : HasPtrRepr,
      B : HasPtrRepr,
      C : HasPtrRepr  {
    fn ptr_repr(self) -> String {
        format!("({},{},{})", self.0.ptr_repr(), self.1.ptr_repr(), self.2.ptr_repr())
    }
}

impl<A : HasPtrRepr> HasPtrRepr for Option<A> {
    fn ptr_repr(self) -> String {
        match self {
            None => format!("n"),
            Some(x) => format!("s{}", x.ptr_repr())

        }
    }
}

// We only use integer slices in the inductive module,
// but they're necessary to avoid either having to add support for
// List(List A), or adding natural number lists as an arena item,
// which is a lot more work than it sounds.
// Slices are printed as either `[]` for the empty list, or
// [n1,n2,..,nN] inline. 
impl HasPtrRepr for &[u16] {
    fn ptr_repr(self) -> String {
        if self.is_empty() {
            format!("[]")
        } else {
            let mut sink = format!("[");
            for elem in self {
                sink.push_str(elem.to_string().as_str());
                sink.push(',');
            }
            assert_eq!(sink.pop(), Some(','));
            sink.push(']');
            sink
        }
    }
}

// String and binderstyle have special representations since
// they're non-recursive and/or non-copy.
impl<'a> HasPtrRepr for StringPtr<'a> {
    fn ptr_repr(self) -> String {
        match self {
            Ptr::E(index, ..) => format!("e{}s", index),
            Ptr::L(index, ..) => format!("l{}s", index),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (string)"),
        }        
    }
}


impl HasPtrRepr for BinderStyle {
    fn ptr_repr(self) -> String {
        match self {
            BinderStyle::Default => format!("d"),
            BinderStyle::Implicit => format!("i"),
            BinderStyle::StrictImplicit => format!("s"),
            BinderStyle::InstImplicit => format!("c"),
        }
    }    
}

impl HasPtrRepr for LocalSerial {
    fn ptr_repr(self) -> String {
        self.0.to_string()
    }
}

// Also special since it's non-recursive. We can just print them
// inline
impl HasPtrRepr for ReducibilityHint {
    fn ptr_repr(self) -> String {
        match self {
            ReducibilityHint::Opaq=> format!("o"),
            ReducibilityHint::Reg(n) => format!("{}", n),
            ReducibilityHint::Abbrev => format!("a"),
        }
    }
}

impl<'a, A : HasPrefix> HasPtrRepr for Ptr<'a, A> {
    fn ptr_repr(self) -> String {
        match self {
            Ptr::E(index, ..) => format!("e{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::L(index, ..) => format!("l{}{}", index, <A as HasPrefix>::PREFIX),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (base)"),
        }
    }
}

impl<'a, A : HasPrefix> HasPtrRepr for ListPtr<'a, A> {
    fn ptr_repr(self) -> String {
        match self {
            Ptr::E(index, ..) => format!("E{}{}", index, <A as HasPrefix>::LIST_PREFIX),
            Ptr::L(index, ..) => format!("L{}{}", index, <A as HasPrefix>::LIST_PREFIX),
            Ptr::P(..) => unreachable!("Should never trace a P pointer (list)"),
        }
    }
}

//impl<'a> HasPtrRepr for Declar<'a> {
//    fn ptr_repr(self) -> String {
//        
//    }
//}

impl<H> HasPtrRepr for Step<H> {
    fn ptr_repr(self) -> String {
        match self {
            Step::Live { step_idx, .. } => step_idx.to_string(),
            _ => panic!("SHould never request ptr_repr from a Pfind step")
        }
    }
}


impl HasPtrRepr for StepIdx {
    fn ptr_repr(self) -> String {
        format!("{}", self)
    }
}

trace_item!{ 'a, Name, trace_name, trace_name_list, 'n', 'N' }
trace_item!{ 'a, Level, trace_level, trace_level_list, 'u', 'U' }
trace_item!{ 'a, Expr, trace_expr, trace_expr_list, 'e', 'E' }
trace_item!{ 'a, RecRule, trace_rec_rule, trace_rec_rule_list, 'r', 'R' }
trace_item!{ 'a, Declar, trace_declar, trace_declar_list, 'd', 'D' }

#[macro_export]
macro_rules! trace_item {
    ( $short:lifetime, $base:ident, $trace_elem:ident, $trace_list:ident, $elem_prefix:literal, $list_prefix : literal ) => {


        impl<$short> HasPrefix for $base<$short> {
            const PREFIX : char = $elem_prefix;
            const LIST_PREFIX : char = $list_prefix;
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

