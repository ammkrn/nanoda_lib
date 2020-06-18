use crate::{ ret_none_if, name, param, arrow, sort, app };
use crate::name::{ NamePtr, NamesPtr, Name, Name::* };
use crate::level::{ LevelPtr, LevelsPtr, Level, Level::* };
use crate::expr::{ Expr, ExprsPtr, ExprPtr, Expr::*, BinderStyle, BinderStyle::* };
use crate::trace::{ IsTracer };
use crate::trace::steps::*;
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


impl<'t, 'l : 't, 'e : 'l> ExprPtr<'l> {
    pub fn infer(
        self,
        flag : InferFlag,
        tc : &mut impl IsTc<'t, 'l, 'e>
    ) -> (ExprPtr<'l>, Step<Infer<'l>>) {
        unimplemented!()
    }
}
