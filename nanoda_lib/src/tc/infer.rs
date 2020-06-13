use crate::{ ret_none_if, name, param, arrow, sort, app };
use crate::name::{ NamePtr, NamesPtr, Name, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle, BinderStyle::* };
//use crate::env::{ Declar, Declar::* };
use crate::trace::{ IsTracer };
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
                    
                    
use InferFlag::*;                    



#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferFlag {
    InferOnly,
    Check
}                