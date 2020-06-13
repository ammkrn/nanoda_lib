use crate::name::{ NamePtr, NamesPtr, StringPtr };
use crate::level::LevelsPtr;
use crate::expr::ExprPtr;
use crate::tc::infer::InferFlag::*;
use crate::quot::add_quot;
use crate::inductive::IndBlock;
use crate::trace::IsTracer;
use crate::utils::{ 
    Tc, 
    Ptr, 
    Env, 
    Live, 
    IsCtx, 
    IsLiveCtx, 
    LiveZst, 
    ListPtr, 
    List::*, 
    Store, 
    HasNanodaDbg 
};

use Notation::*;
use ReducibilityHint::*;
use Declar::*;
use DeclarSpec::*;

pub type DeclarPtr<'a> = Ptr<'a, Declar<'a>>;
pub type DeclarsPtr<'a> = ListPtr<'a, Declar<'a>>;
pub type RecRulePtr<'a> = Ptr<'a, RecRule<'a>>;
pub type RecRulesPtr<'a> = ListPtr<'a, RecRule<'a>>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Notation<'a> {
    Prefix  { name : NamePtr<'a>, priority : usize, oper : StringPtr<'a> },
    Infix   { name : NamePtr<'a>, priority : usize, oper : StringPtr<'a> },
    Postfix { name : NamePtr<'a>, priority : usize, oper : StringPtr<'a> },
}

impl<'a> Notation<'a> {
    pub fn new_prefix(name : NamePtr<'a>, priority : usize, oper : StringPtr<'a>) -> Self {
        Prefix { name, priority, oper }
    }

    pub fn new_infix(name : NamePtr<'a>, priority : usize, oper : StringPtr<'a>) -> Self {
        Infix { name, priority, oper }
    }

    pub fn new_postfix(name : NamePtr<'a>, priority : usize, oper : StringPtr<'a>) -> Self {
        Postfix { name, priority, oper }
    }
}

#[derive(Debug)]
pub enum DeclarSpec<'a> {
    AxiomSpec {
        name : NamePtr<'a>,
        type_ : ExprPtr<'a>,
        uparams : LevelsPtr<'a>,
        is_unsafe : bool,
    },
    DefinitionSpec {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        is_unsafe : bool,
    },
    TheoremSpec {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    OpaqueSpec {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    QuotSpec,
    InductiveSpec(IndBlock<'a>),
}


impl<'l, 'e : 'l> DeclarSpec<'e> {
    pub fn new_axiom(
        name : NamePtr<'e>,
        uparams : LevelsPtr<'e>,
        type_ : ExprPtr<'e>,
        is_unsafe : bool
    ) -> Self {
        assert!(name.in_env() && uparams.in_env() && type_.in_env()); 
        AxiomSpec {
            name,
            uparams,
            type_,
            is_unsafe,
        }
    }

    pub fn new_def(
        name : NamePtr<'e>,
        uparams : LevelsPtr<'e>,
        type_ : ExprPtr<'e>,
        val : ExprPtr<'e>,
        is_unsafe : bool
    ) -> Self {
        assert!(name.in_env() && uparams.in_env() && type_.in_env() && val.in_env()); 
        DefinitionSpec {
            name,
            uparams,
            type_,
            val,
            is_unsafe,
        }
    }    

    pub fn new_quot() -> Self {
        QuotSpec
    }    

    pub fn new_inductive(indblock : IndBlock<'e>) -> Self {
        InductiveSpec(indblock)
    }        
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecRule<'a> {
    pub cnstr_name : NamePtr<'a>,
    pub num_fields : u16,
    pub val : ExprPtr<'a>
}

impl<'a> RecRule<'a> {
    pub fn new(cnstr_name : NamePtr<'a>, num_fields : u16, val : ExprPtr<'a>) -> Self {
        RecRule {
            cnstr_name,
            num_fields,
            val
        }
    }

    pub fn insert_env<'e>(
        self, 
        env : &mut Env<'e, impl 'e + IsTracer>, 
        live : &Store<LiveZst>
    ) -> RecRulePtr<'e> {
        RecRule {
            cnstr_name : self.cnstr_name.insert_env(env, live),
            num_fields : self.num_fields,
            val : self.val.insert_env(env, live)
        }.alloc(env)
    }
}



impl<'a> HasNanodaDbg<'a> for RecRule<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        format!("RecRule( cnstr_name : {}, num_fields : {}, val : {})", 
        self.cnstr_name.nanoda_dbg(ctx), 
        self.num_fields,
        self.val.nanoda_dbg(ctx))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Declar<'a> {
    Axiom {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        is_unsafe : bool,
    },
    Definition {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        hint : ReducibilityHint,
        is_unsafe : bool,
    },
    Theorem {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    Opaque {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
    },
    Quot {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
    },
    Inductive {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        num_params : u16,
        all_ind_names : NamesPtr<'a>,
        all_cnstr_names : NamesPtr<'a>,
        //pub is_rec : bool,
        //pub is_reflexive : bool,
        is_unsafe : bool,
    },
    Constructor {
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        parent_name : NamePtr<'a>,
        num_fields : u16,
        minor_idx : u16,
        num_params : u16,
        is_unsafe : bool,        
    },
    Recursor {
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




impl<'a> Declar<'a> {
    pub fn get_hint(self) -> ReducibilityHint {
        match self {
            Definition { hint, .. } => hint,
            owise => unreachable!("Only Definition declars have a reducibility hint! found {:#?}", owise)
        }
    }

    pub fn rec_num_params(&self) -> Option<u16> {
        match self {
            Recursor { num_params, .. } => Some(*num_params),
            _ => None
        }
    }

    pub fn rec_num_motives(&self) -> Option<u16> {
        match self {
            Recursor { num_motives, .. } => Some(*num_motives),
            _ => None
        }
    }

    pub fn rec_num_minors(&self) -> Option<u16> {
        match self {
            Recursor { num_minors, .. } => Some(*num_minors),
            _ => None
        }
    }

    pub fn rec_major_idx(&self) -> Option<u16> {
        match self {
            Recursor { major_idx, .. } => Some(*major_idx),
            _ => None
        }
    }

    pub fn rec_is_k(&self) -> Option<bool> {
        match self {
            Recursor { is_k, .. } => Some(*is_k),
            _ => None
        }
    }


    pub fn name(&self) -> NamePtr<'a> {
        match self {
            | Axiom       { name, .. }
            | Definition  { name, .. }
            | Theorem     { name, .. }
            | Opaque      { name, .. }
            | Quot        { name, .. }
            | Inductive   { name, .. }
            | Constructor { name, .. }
            | Recursor    { name, .. } => *name,
        }
    }

    pub fn uparams(&self) -> LevelsPtr<'a> {
        match self {
            | Axiom       { uparams, .. }
            | Definition  { uparams, .. }
            | Theorem     { uparams, .. }
            | Opaque      { uparams, .. }
            | Quot        { uparams, .. }
            | Inductive   { uparams, .. }
            | Constructor { uparams, .. }
            | Recursor    { uparams, .. } => *uparams,
        }
    }

    pub fn type_(&self) -> ExprPtr<'a> {
        match self {
            | Axiom       { type_, .. }
            | Definition  { type_, .. }
            | Theorem     { type_, .. }
            | Opaque      { type_, .. }
            | Quot        { type_, .. }
            | Inductive   { type_, .. }
            | Constructor { type_, .. } 
            | Recursor    { type_, .. } => *type_,
        }
    }

    pub fn is_unsafe(&self) -> bool {
        match self {
            Theorem  {..}
            | Opaque {..}
            | Quot   {..} => false,
            | Axiom       { is_unsafe, .. }
            | Definition  { is_unsafe, .. }
            | Inductive   { is_unsafe, .. }
            | Constructor { is_unsafe, .. }
            | Recursor    { is_unsafe, .. } => *is_unsafe,
        }
    }

    pub fn insert_env<'e>(
        self, 
        env : &mut Env<'e, impl 'e + IsTracer>, 
        live : &Store<'a, LiveZst>
    ) -> DeclarPtr<'e> {
        let name = self.name().insert_env(env, live);
        let uparams = self.uparams().insert_env(env, live);
        let type_ = self.type_().insert_env(env, live);
        match self {
            Axiom { is_unsafe, .. } => {
                Axiom { 
                    name, 
                    uparams, 
                    type_, 
                    is_unsafe 
                }.alloc(env)
            },
            Definition { val, hint, is_unsafe, ..  } => {
                Definition {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                    hint,
                    is_unsafe,
                }.alloc(env)
            },
            Theorem { val, ..  } => {
                Theorem {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                }.alloc(env)
            },
            Opaque { val, ..  } => {
                Opaque {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                }.alloc(env)
            },
            Quot { .. } => {
                Quot {
                    name,
                    uparams,
                    type_
                }.alloc(env)
            },
            Inductive { num_params, all_ind_names, all_cnstr_names, is_unsafe, .. } => {
                Inductive {
                    name,
                    uparams,
                    type_,
                    num_params,
                    all_ind_names : all_ind_names.insert_env(env, live),
                    all_cnstr_names : all_cnstr_names.insert_env(env, live),
                    is_unsafe
                }.alloc(env)
            },
            Constructor { parent_name, num_fields, minor_idx, num_params, is_unsafe, .. } => {
                Constructor {
                    name,
                    uparams,
                    type_,
                    parent_name : parent_name.insert_env(env, live),
                    num_fields,
                    minor_idx,
                    num_params,
                    is_unsafe
                }.alloc(env)
            },
            Recursor { all_names, num_params, num_indices, num_motives, num_minors, major_idx, rec_rules, is_k, is_unsafe, .. } => {
                Recursor {
                    name,
                    uparams,
                    type_,
                    all_names : all_names.insert_env(env, live),
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    major_idx,
                    rec_rules : rec_rules.insert_env(env, live),
                    is_k,
                    is_unsafe
                }.alloc(env)
            }
        }
    }        


}


impl<'a> HasNanodaDbg<'a> for Declar<'a> {
    fn nanoda_dbg(self, _ctx : &impl IsCtx<'a>) -> String {
        unimplemented!()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReducibilityHint {
    Opaq,
    Reg(u16),
    Abbrev,
}

