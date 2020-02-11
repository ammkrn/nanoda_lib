use crate::name::Name;
use crate::level::Level;
use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveType {
    pub name : Name,
    pub type_ : Expr,
    pub constructors : Vec<Constructor>
}

impl InductiveType {
    pub fn new(name : Name, type_ : Expr, constructors : Vec<Constructor>) -> Self {
        InductiveType {
            name,
            type_,
            constructors
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Constructor {
    pub name : Name,
    pub type_ : Expr,
}


impl Constructor {
    pub fn new(name : &Name, type_ : &Expr) -> Self {
        Constructor {
            name : name.clone(),
            type_ : type_.clone()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveDeclar {
    pub name : Name,
    pub lparams : Vec<Level>,
    pub num_params : usize,
    pub types : Vec<InductiveType>,
    pub is_unsafe : bool,
}



impl InductiveDeclar {
    pub fn new(name : Name,
               lparams : Vec<Level>, 
               num_params : usize, 
               types : Vec<InductiveType>,
               is_unsafe : bool) -> InductiveDeclar {
        InductiveDeclar {
            name,
            lparams,
            num_params,
            types,
            is_unsafe
        }
   }

}

pub fn get_all_inductive_names(v : &Vec<InductiveType>) -> Vec<Name> {
    v.into_iter().map(|d| d.name.clone()).collect::<Vec<Name>>()
}


