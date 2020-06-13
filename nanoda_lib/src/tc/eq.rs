use crate::ret_none_if;
use crate::{ name, param, arrow, sort, app };
use crate::name::{ NamePtr, NamesPtr, Name, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle, BinderStyle::* };
use crate::tc::infer::InferFlag::*;
//use crate::env::{ Declar, Declar::* };
use crate::trace::IsTracer;
use crate::trace::steps::{ WhnfCore, Delta };
use crate::utils::{ 
    Ptr,
    List::*,
    ListPtr,
    Env,
    IsTc,
    Tc,
    Pfinder,
    HasNanodaDbg 
};

use ShortCircuit::*;
use DeltaResult::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShortCircuit {
    EqShort,
    NeqShort
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeltaResult<'a> {
    Short(ShortCircuit),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}