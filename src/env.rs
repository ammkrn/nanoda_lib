use std::cmp::{ Ordering, Ordering::* };

use std::sync::Arc;
use hashbrown::HashMap;
use parking_lot::RwLock;

use crate::name::Name;
use crate::level::Level;
use crate::expr::{ Expr, unique_const_names };
use crate::recursor::RecursorVal;
use crate::inductive::newinductive::InductiveDeclar;
use crate::inductive::addinductive::AddInductiveFn;
use crate::tc::TypeChecker;
use crate::utils::ShortCircuit::*;
use crate::errors::{ NanodaResult, NanodaErr::* };
use enum_tools::Get;

use ConstantInfo::*;
use ReducibilityHint::*;
use Notation::*;

pub type ArcEnv = Arc<RwLock<Env>>;

// At some point in the future when mutuals and whatnot get added
// Declaration will have to be a separately tracked thing again.
#[derive(Clone)]
pub struct Env {
    pub constant_infos : HashMap<Name, ConstantInfo>,
    pub notations : HashMap<Name, Notation>,
    pub quot_is_init : bool,
}

impl std::cmp::PartialEq for Env {
    fn eq(&self, _other : &Env) -> bool { true }
}

impl std::cmp::Eq for Env {}

impl std::fmt::Debug for Env {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "ENV")
    }
}

// Most of the `get_` methods on this have to clone and return 
// by value since they're behind an RwLock.
impl Env {
    pub fn new_arc_env(num_mods : Option<usize>) -> ArcEnv {
        Arc::new(RwLock::new(Env::new(num_mods.unwrap_or(10_000))))
    }

    fn new(num_mods : usize) -> Self {
        Env {
            constant_infos : HashMap::with_capacity(num_mods),
            notations : HashMap::with_capacity(500),
            quot_is_init : false,
        }
    }

    pub fn num_items(&self) -> usize {
        self.constant_infos.len()
    }


    pub fn add_constant_info(&mut self, c : ConstantInfo) {
        self.constant_infos.insert(c.get_constant_base().name.clone(), c);
    }

    pub fn get_constant_info(&self, n : &Name) -> Option<ConstantInfo> {
        self.constant_infos.get(n).cloned()
    }


    pub fn get_first_constructor_name(&self, n : &Name) -> Option<Name> {
        match self.get_constant_info(n) {
            Some(InductiveInfo(InductiveVal { cnstrs, .. })) => cnstrs.get(0).cloned(),
            _ => None,
        }
    }

    pub fn add_notation(&mut self, n : &Name, notation: Notation) {
        match self.notations.get(n) {
            Some(_) => (),
            None => { self.notations.insert(n.clone(), notation); }
        }
    }

    pub fn get_recursor_val(&self, n : &Name) -> Option<RecursorVal> {
        match self.constant_infos.get(n)? {
            ConstantInfo::RecursorInfo(rec_val) => Some(rec_val.clone()),
            _ => None
        }
    }

    pub fn ensure_not_dupe_name(&self, n : &Name) {
        if self.constant_infos.contains_key(n) {
            panic!("constant_base name {} was already declared!\n", n);
        }
    }
}

pub fn ensure_no_dupe_lparams(v : &Vec<Level>) -> NanodaResult<()> {
    for (idx, elem) in v.iter().enumerate() {
        let slice = &v[idx+1..];
        if slice.contains(elem) {
            return Err(DupeLparamErr(file!(), line!(), idx))
        }
    }
    Ok(())
}



// declaration.h ~69; This is just stored in OTHER val items.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstantBase {
    pub name : Name,
    pub lparams : Vec<Level>,
    pub type_ : Expr
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AxiomVal {
    pub constant_base : ConstantBase,
    pub is_unsafe : bool
}

impl AxiomVal {
    pub fn new(name : Name, lparams : Vec<Level>, type_ : Expr, is_unsafe : Option<bool>) -> Self {
        let constant_base = ConstantBase::new(name, lparams, type_);
        AxiomVal {
            constant_base,
            is_unsafe : is_unsafe.unwrap_or(false)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefinitionVal {
    pub constant_base : ConstantBase,
    pub value : Expr,
    pub hint : ReducibilityHint,
    pub is_unsafe : bool
}

impl DefinitionVal {
    pub fn new(env : ArcEnv, name : Name, lvls : Vec<Level>, ty : Expr, value : Expr) -> Self {
        let height_usize = match unique_const_names(&value)
                           .iter()
                           .filter_map(|name| env.read().get_hint(name))
                           .filter_map(|hint| hint.as_usize())
                           .max() {
                               Some(h) => h + 1,
                               _ => 1
                           };

        let hint = Regular(height_usize);
        let constant_base = ConstantBase::new(name, lvls, ty);
        DefinitionVal {
            constant_base,
            value,
            hint,
            is_unsafe : false
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TheoremVal {
    pub constant_base : ConstantBase,
    pub value : Expr
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OpaqueVal {
    pub constant_base : ConstantBase,
    pub value : Expr
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuotVal {
    pub constant_base : ConstantBase,
}

impl QuotVal {
    pub fn from_const_val(c : ConstantBase) -> Self {
        QuotVal {
            constant_base : c,
        }
    }

}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveVal {
    constant_base : ConstantBase,
    pub nparams : usize,
    pub nindices : usize,
    pub all : Vec<Name>,
    pub cnstrs : Vec<Name>,
    pub is_rec : bool,
    pub is_unsafe : bool,
    pub is_reflexive : bool
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorVal {
    constant_base : ConstantBase,
    pub induct : Name,
    pub cidx : usize,
    pub nparams : usize,
    pub nfields : usize,
    pub is_unsafe : bool,
}

impl ConstructorVal {
    // declaration.cpp ~78
    // extends constant_base
    pub fn new(name : Name,
               lparams : Vec<Level>,
               type_ : Expr,
               induct : Name,  
               cidx : usize, 
               nparams : usize, 
               nfields : usize, 
               is_unsafe : bool) -> Self {
        let constant_base = ConstantBase::new(name.clone(), lparams.clone(), type_.clone());

        ConstructorVal {
            constant_base,
            induct,
            cidx,
            nparams,
            nfields,
            is_unsafe
        }
    }

}



// CPP declaration.h ~424
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantInfo {
    AxiomInfo(AxiomVal),
    DefinitionInfo(DefinitionVal),
    TheoremInfo(TheoremVal),
    OpaqueInfo(OpaqueVal),
    QuotInfo(QuotVal),
    InductiveInfo(InductiveVal),
    ConstructorInfo(ConstructorVal),
    RecursorInfo(RecursorVal),
}



impl ConstantInfo {

    pub fn get_hint(&self) -> ReducibilityHint {
        match self {
            DefinitionInfo(DefinitionVal { hint, .. }) => *hint,
            _ => unreachable!("Should never call 'get_hints' on a non-def ")
        }
    }
    // While all 'Const' items have a type, only definitions and theorems 
    // have a value level Expr item. (IE Pi x, lambda x...)
    pub fn has_value(&self, _allow_opaque : Option<bool>) -> bool {
        let allow_opaque = _allow_opaque.unwrap_or(false);

        match self {
            TheoremInfo(..) | DefinitionInfo(..) => true,
            OpaqueInfo(..) if allow_opaque => true,
            _ => false
        }
    }

    fn get_value_core(&self, maybe_debug_bool_allow_opaque : bool) -> Expr {
        assert!(self.has_value(Some(maybe_debug_bool_allow_opaque)));
        match self {
            TheoremInfo(TheoremVal { value, .. }) => value.clone(),
            DefinitionInfo(DefinitionVal { value, .. }) => value.clone(),
            OpaqueInfo(OpaqueVal { .. }) if maybe_debug_bool_allow_opaque => {
                unreachable!("maybe_debug should always be false");
                //value.clone()
            },
            _ => unreachable!()
        }
    }

    pub fn get_value(&self) -> Expr {
        self.get_value_core(false)
    }

    pub fn get_value_option(&self) -> Option<Expr> {
        match self {
            TheoremInfo(TheoremVal { value, .. }) => Some(value.clone()),
            DefinitionInfo(DefinitionVal { value, .. }) => Some(value.clone()),
            OpaqueInfo(OpaqueVal { value, .. }) => Some(value.clone()),
            _ => None
        }
    }

    pub fn get_constant_base(&self) -> &ConstantBase {
        match self {
            AxiomInfo(x) => &x.constant_base,
            DefinitionInfo(x) => &x.constant_base,
            TheoremInfo(x) => &x.constant_base,
            OpaqueInfo(x) => &x.constant_base,
            InductiveInfo(x) => &x.constant_base,
            ConstructorInfo(x) => &x.constant_base,
            RecursorInfo(x) => &x.constant_base,
            QuotInfo(x) => &x.constant_base,
        }
    }

    pub fn get_name(&self) -> &Name {
        &self.get_constant_base().name
    }

    pub fn get_lparams(&self) -> &Vec<Level> {
        &self.get_constant_base().lparams
    }

    pub fn get_type(&self) -> &Expr {
        &self.get_constant_base().type_
    }


    pub fn is_unsafe(&self) -> bool {
        match self {
            AxiomInfo(x) => x.is_unsafe,
            DefinitionInfo(x) => x.is_unsafe,
            TheoremInfo(_) => false,
            OpaqueInfo(_) => false,
            QuotInfo(_) => false,
            InductiveInfo(x) => x.is_unsafe,
            ConstructorInfo(x) => x.is_unsafe,
            RecursorInfo(x) => x.is_unsafe,

        }
    }
}

impl ConstantBase {
    pub fn new(name : Name, lparams : Vec<Level>, type_ : Expr) -> Self {
        ConstantBase {
            name,
            lparams,
            type_
        }
    }
}

impl InductiveVal {
    // name must equal all_used(0)
    // extends constant_base
    pub fn new(name : Name,
               lparams : Vec<Level>,
               type_ : Expr,
               nparams : usize,
               nindices : usize,
               all : Vec<Name>,
               cnstrs : Vec<Name>,
               is_rec : bool,
               is_unsafe : bool,
               is_reflexive : bool) -> Self {
        assert!(&name == &all[0]);
        let constant_base = ConstantBase::new(name, lparams, type_);
        InductiveVal {
            constant_base,
            nparams,
            nindices,
            all,
            cnstrs,
            is_rec,
            is_unsafe,
            is_reflexive
        }
    }
}



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReducibilityHint {
    Regular(usize),
    Opaque,
    Abbreviation,
}

impl ReducibilityHint {
    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Regular(x) => Some(*x),
            _ => None
        }
    }
   
   pub fn compare(self, other : ReducibilityHint) -> Ordering {
        match (self, other) {
            (Regular(h1), Regular(h2)) if h1 == h2 => Equal,
            (Regular(h1), Regular(h2)) if h1 > h2 => Greater,
            (Regular(h1), Regular(h2)) if h1 < h2 => Less,
            (Opaque, Opaque) | (Abbreviation, Abbreviation) => Equal,
            (Opaque, _) => Less,
            (_, Opaque) => Greater,
            (Abbreviation, _) => Greater,
            (_, Abbreviation) => Less,
            _ => unreachable!()
        }
    }
}

impl Env {
    pub fn init_quot(&mut self) {
        self.quot_is_init = true;
    }
    pub fn get_hint(&self, name : &Name) -> Option<ReducibilityHint> {
        match self.constant_infos.get(name) {
            Some(DefinitionInfo(def_val)) => Some(def_val.hint),
            Some(_) => None,
            None => None
        }
    }
}


// Checking a `ConstantBase` consists of :
// 1. Making sure it has no duplicate universe parameters
// 2. Inferring its type with `checked_infer`
// 3. Ensuring that the inferred type is a Sort (since ConstantBase is itself a type,
//    its inferred type must therefore be a sort)
pub fn check_constant_base(c : &ConstantBase, tc : &mut TypeChecker) -> NanodaResult<()> {
    tc.env.read().ensure_not_dupe_name(&c.name);
    ensure_no_dupe_lparams(&c.lparams)?;
    assert!(!c.type_.has_locals());
    c.type_
     .checked_infer(c.lparams.clone(), tc)
     .ensure_sort(tc);
    Ok(())
}

pub fn check_constant_base_new_tc(env : ArcEnv, c : &ConstantBase, safe_only : bool) -> NanodaResult<()> {
    let mut tc = TypeChecker::new(Some(safe_only), env.clone());
    check_constant_base(c, &mut tc)
}

pub fn add_axiom(ax : AxiomVal, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    if _check {
        check_constant_base_new_tc(env.clone(), &ax.constant_base, ax.is_unsafe)?
    } 

    Ok(env.write().add_constant_info(AxiomInfo(ax)))
}

// I'm not yet sure what all the nuances of Lean4's `unsafe` tag are;
// if you're checking a Lean 3 export file, you won't come across any `unsafe`
// definitions, so we'll be in the else branch.
// Checking a safe definition consists of:
// 1. checking its `constant_base` declaration 
//       1a. Making sure it's name hasn't already been used 
//       1b. Making sure it has no duplicate universe parameters
//       1c. Making sure its declared type is well-formed
// 2. inferring the type of its value
// 3. ensuring that the inferred type of its value is definitionally equal
//    to the type it claims to have.
pub fn add_definition(def : DefinitionVal, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    // If it's unsafe, we need to add its `constant_base` to the environment,
    // then we can check its value level stuff.
    if def.is_unsafe {
        if _check {
            let safe_only = false;
            let mut tc = TypeChecker::new(Some(safe_only), env.clone());
            check_constant_base(&def.constant_base, &mut tc)?;
        }

        env.write().add_constant_info(DefinitionInfo(def.clone()));

        if _check {
            let safe_only = false;
            let mut tc = TypeChecker::new(Some(safe_only), env.clone());
            let val_type = def.value.checked_infer(def.constant_base.lparams.clone(), &mut tc);
            if (val_type.check_def_eq(&def.constant_base.type_, &mut tc) == NeqShort) {
                return Err(TcNeqErr(file!(), line!()))
            }
        }
        Ok(())
    } else {
        if _check {
            let mut tc = TypeChecker::new(None, env.clone());
            check_constant_base(&def.constant_base, &mut tc)?;
            let val_type = def.value.checked_infer(def.constant_base.lparams.clone(), &mut tc);
 
            if (val_type.check_def_eq(&def.constant_base.type_, &mut tc) == NeqShort) {
                return Err(TcNeqErr(file!(), line!()))
            } 
        } 
        Ok(env.write().add_constant_info(DefinitionInfo(def)))
    }
}

pub fn add_quot(quot : QuotVal, env : ArcEnv) -> NanodaResult<()> {
    check_constant_base_new_tc(env.clone(), &quot.constant_base, false)?;


    Ok(env.write().add_constant_info(QuotInfo(quot)))
}



// Exactly the same as the `is_safe` branch of add_definition
#[allow(dead_code)]
pub fn add_theorem(thm : TheoremVal, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    // FIXME there's a `TODO` in the CPP version here.
    if _check {
        let safe_only = false;
        let mut tc = TypeChecker::new(Some(safe_only), env.clone());
        check_constant_base(&thm.constant_base, &mut tc)?;

        let val_type = thm.value.checked_infer(thm.constant_base.lparams.clone(), &mut tc);

        if (val_type.check_def_eq(&thm.constant_base.type_, &mut tc) == NeqShort) {
            return Err(TcNeqErr(file!(), line!()))
        }
    }
    Ok(env.write().add_constant_info(TheoremInfo(thm)))
}




// Exactly the same as the `is_safe` branch of add_definition.
#[allow(dead_code)]
fn add_opaque(opaque : OpaqueVal, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    if _check {
        let safe_only = false;
        let mut tc = TypeChecker::new(Some(safe_only), env.clone());
        check_constant_base(&opaque.constant_base, &mut tc)?;

        let val_type = opaque.value.checked_infer(opaque.constant_base.lparams.clone(), &mut tc);

        if (val_type.check_def_eq(&opaque.constant_base.type_, &mut tc) == NeqShort) {
            return Err(TcNeqErr(file!(), line!()))
        }
    }

    Ok(env.write().add_constant_info(OpaqueInfo(opaque)))
}

// because they're mutual, they need a special procedure that's essentially
// batch application of the `is_unsafe` branch of add_definition :
// 1. check `constant_base` cores,
// 2. then add all definitions to env
// 3. check the types of the definitions' values match their ascribed types.
#[allow(dead_code)]
fn add_mutual(defs : Vec<DefinitionVal>, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    if _check {
        let safe_only = false;
        let mut tc = TypeChecker::new(Some(safe_only), env.clone());

        for def in defs.iter() {
            if (!def.is_unsafe) {
                panic!("mutual definition was not marked as `meta`; this is verboten.")
            }
            check_constant_base(&def.constant_base, &mut tc)?;
        }
    }

    for def in defs.iter().cloned() {
        env.write().add_constant_info(DefinitionInfo(def));
    }

    if _check {
        let safe_only = false;
        let mut tc = TypeChecker::new(Some(safe_only), env.clone());
        for def in defs.iter() {
            let val_type = def.value.checked_infer(def.constant_base.lparams.clone(), &mut tc);
            if (val_type.check_def_eq(&def.constant_base.type_, &mut tc) == NeqShort) {
                panic!("error when checking val of mutual def {}", &def.constant_base.name);
            }
        }
    }

    Ok(())
}

// The tracing attribute on this one is over `AddInductiveFn::add_inductive_core`
pub fn add_inductive(ind : InductiveDeclar, env : ArcEnv, _check : bool) -> NanodaResult<()> {
    AddInductiveFn::new(ind.name, 
                        ind.lparams, 
                        ind.num_params, 
                        ind.is_unsafe, 
                        ind.types, 
                        env).add_inductive_core()
}


#[derive(Clone, PartialEq, Get)]
pub enum Notation {
    Prefix  { name : Name, priority : usize, oper : String },
    Infix   { name : Name, priority : usize, oper : String },
    Postfix { name : Name, priority : usize, oper : String },
}


impl Notation {
    pub fn new_prefix(name : Name, priority : usize, oper : String) -> Self {
        Prefix { name, priority, oper }
    }

    pub fn new_infix(name : Name, priority : usize, oper : String) -> Self {
        Infix { name, priority, oper }
    }

    pub fn new_postfix(name : Name, priority : usize, oper : String) -> Self {
        Postfix { name, priority, oper }
    }
}