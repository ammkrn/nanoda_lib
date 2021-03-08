use crate::name::{ NamePtr, NamesPtr, StringPtr };
use crate::level::LevelsPtr;
use crate::expr::ExprPtr;
use crate::tc::infer::InferFlag::*;
use crate::quot::add_quot;
use crate::inductive::IndBlock;
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
    pub fn new_axiom(name : NamePtr<'e>,
                     uparams : LevelsPtr<'e>,
                     type_ : ExprPtr<'e>,
                     is_unsafe : bool) -> Self {
        assert!(name.in_env() && uparams.in_env() && type_.in_env()); 
        AxiomSpec {
            name,
            uparams,
            type_,
            is_unsafe,
        }
    }

    pub fn new_def(name : NamePtr<'e>,
                   uparams : LevelsPtr<'e>,
                   type_ : ExprPtr<'e>,
                   val : ExprPtr<'e>,
                   is_unsafe : bool) -> Self {
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

    pub fn compile(self, compiler : &mut Live<'l, 'e>) {
        match self {
            AxiomSpec { name, uparams, type_, is_unsafe } => {
                if compiler.debug_mode() {
                    println!("compiling axiom: {}", name.nanoda_dbg(compiler));
                }
                let d = Axiom {
                    name,
                    uparams,
                    type_,
                    is_unsafe,
                };
                compiler.admit_declar(d);
            },
            DefinitionSpec { name, uparams, type_, val, is_unsafe } => {
                if compiler.debug_mode() {
                    println!("compiling def : {}", name.nanoda_dbg(compiler));
                }
                let d = Definition {
                    name,
                    uparams,
                    type_,
                    val,
                    hint : Reg(val.calc_height(compiler)),
                    is_unsafe,
                };
                compiler.admit_declar(d);
            }
            TheoremSpec {..} => {
                unimplemented!("Theorem not yet implemented")
            }
            OpaqueSpec {..} => {
                unimplemented!("Opaque not yet implemented")
            },
            QuotSpec => {
                if compiler.debug_mode() {
                    println!("compiling quot")
                }
                add_quot(compiler)
            }
            // Right now, the compilation step for inductive also includes
            // all of their checks. Breaking them out would require making 
            // annoying changes to the inductive module, and as things are now
            // (it might change with mutuals) they're extremely cheap to check
            // compared to definitions, so I'm just going to let it rock.
            InductiveSpec(mut indblock) => {
                if compiler.debug_mode() {
                    println!("compiling inductive: {}", indblock.ind_names.nanoda_dbg(compiler));
                }
                indblock.declare_ind_types(compiler);
                indblock.mk_local_indices(compiler);
                indblock.declare_cnstrs(compiler);
                indblock.mk_elim_level(compiler);
                indblock.init_k_target(compiler);
                indblock.mk_majors_wrapper(compiler);
                indblock.mk_motives_wrapper(compiler);
                indblock.mk_minors_wrapper(compiler);
                indblock.declare_rec_rules(compiler);
                indblock.declare_recursors(compiler);                
            }
        }
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
        env : &mut Env<'e>, 
        live : &Store<LiveZst>
    ) -> RecRulePtr<'e> {
        RecRule {
            cnstr_name : self.cnstr_name.insert_env(env, live),
            num_fields : self.num_fields,
            val : self.val.insert_env(env, live)
        }.alloc(env)
    }
}

fn get_rec_rule_aux<'a>(
    rem_rules : ListPtr<'a, RecRule<'a>>,
    c_name : NamePtr<'a>,
    ctx : &impl IsLiveCtx<'a>
) -> Option<RecRulePtr<'a>> {
    match rem_rules.read(ctx) {
        Cons(hd, _) if hd.read(ctx).cnstr_name == c_name => Some(hd),
        Cons(_, tl) => get_rec_rule_aux(tl, c_name, ctx),
        Nil => None
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

    pub fn get_rec_rule(
        self, 
        major : ExprPtr<'a>, 
        ctx : &impl IsLiveCtx<'a>
    ) -> Option<RecRulePtr<'a>> {
        match self {
            Recursor { rec_rules, .. } => {
                let (c_name, _) = major.unfold_apps_fun(ctx).try_const_info(ctx)?;
                get_rec_rule_aux(rec_rules, c_name, ctx)
            },
            _ => None
        }
    }    

    pub fn new_axiom(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        is_unsafe : bool
    ) -> Self {
        Axiom {
            name,
            uparams,
            type_,
            is_unsafe
        }
    }

    pub fn new_definition(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        is_unsafe : bool,
        live : &mut Live<'a, '_>
    ) -> Self {
        Definition {
            name,
            uparams,
            type_,
            val,
            hint : Reg(val.calc_height(live)),
            is_unsafe
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

    pub fn new_inductive(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        num_params : u16,
        all_ind_names : NamesPtr<'a>,
        all_cnstr_names : NamesPtr<'a>,
        //is_rec : bool,
        //is_reflexive : bool,
        is_unsafe : bool
    ) -> Self {
        Inductive {
            name,
            uparams,
            type_,
            num_params,
            all_ind_names,
            all_cnstr_names,
            //is_rec,
            //is_reflexive,
            is_unsafe
        }
    }    

    pub fn new_cnstr<'e>(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        parent_name : NamePtr<'a>,
        num_params : u16,
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e>
    ) -> Self {
        Constructor {
            name,
            uparams,
            type_,
            parent_name,
            num_fields : type_.telescope_size(ctx) - num_params,
            num_params,
            is_unsafe
        }
    }      

    pub fn new_recursor(
        name : NamePtr<'a>,
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
        is_unsafe : bool
    ) -> Self {
        Recursor {
            name,
            uparams,
            type_,
            all_names,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            major_idx,
            rec_rules,
            is_k,
            is_unsafe,
        }
    }       

    pub fn insert_env<'e>(
        self, 
        env : &mut Env<'e>, 
        live : &Store<'a, LiveZst>
    ) -> Declar<'e> {
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
                }
            },
            Definition { val, hint, is_unsafe, ..  } => {
                Definition {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                    hint,
                    is_unsafe,
                }
            },
            Theorem { val, ..  } => {
                Theorem {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                }
            },
            Opaque { val, ..  } => {
                Opaque {
                    name,
                    uparams,
                    type_,
                    val : val.insert_env(env, live),
                }
            },
            Quot { .. } => {
                Quot {
                    name,
                    uparams,
                    type_
                }
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
                }
            },
            Constructor { parent_name, num_fields, num_params, is_unsafe, .. } => {
                Constructor {
                    name,
                    uparams,
                    type_,
                    parent_name : parent_name.insert_env(env, live),
                    num_fields,
                    num_params,
                    is_unsafe
                }
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
                }
            }
        }
    }        

    pub fn check<'l>(self, _should_check : bool, live : &mut Live<'l, 'a>) {
        match self {
            Axiom { name, uparams, type_, .. } => {
                if live.debug_mode() {
                    println!("checking axiom: {}", name.nanoda_dbg(live));
                }
                check_vitals(name, uparams, type_, live);
            },            
            Definition { name, uparams, type_, val, is_unsafe, .. } if !is_unsafe => {
                if live.debug_mode() {
                    println!("checking def: {}", name.nanoda_dbg(live));
                }
                {
                    let mut tc = live.as_tc(Some(uparams), None);
                    check_vitals_w_tc(name, uparams, type_, &mut tc);
                    let val_type = val.infer(Check, &mut tc);
                    val_type.assert_def_eq(type_, &mut tc);
                }
            },
            Definition {..} => {
                unimplemented!("unsafe declar");
                //assert!(is_unsafe);
                //if should_check {
                //    // FIXME handle safe_only flag properly
                //    let mut tc = live.get_tc(Some(uparams));
                //    check_vitals_w_tc(name, uparams, type_, &mut tc);
                //}

                //let declar = Declar::new_definition(name, uparams, type_, val, is_unsafe, live);
                //live.admit_declar(declar);

                //if should_check {
                //    let mut tc = live.get_tc(Some(uparams));
                //    let val_type = val.infer(Check, &mut tc);
                //    assert!(val_type.def_eq(type_, &mut tc).is_eq_short());
                //}
            },        
            
            // All of these are done in `compile` right now.
            // See the comment in that method.
            Quot {..} => (),
            Inductive {..} => (),
            Constructor {..} => (),
            Recursor {..} => (),
            Theorem {..} => unimplemented!("Theorem not implemented in lean3!"),
            Opaque {..} => unimplemented!("Opaque not implemented in lean3!")
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


// We reuse the typechecker for definitions, so the inference
// will be a cache hit.
pub fn check_vitals_w_tc<'t, 'l : 't, 'e : 'l>(
    name : NamePtr<'l>,
    uparams : LevelsPtr<'l>,
    type_ : ExprPtr<'l>,
    tc : &mut Tc<'t, 'l, 'e>
) {
    assert!(name.in_env());
    assert!(uparams.in_env());
    assert!(type_.in_env());
    assert!(uparams.no_dupes(tc));
    assert!(!type_.has_locals(tc));
    let inferred_type = type_.infer(Check, tc);
    inferred_type.ensure_sort(tc);
}

pub fn check_vitals<'t, 'l : 't, 'e : 'l>(
    name : NamePtr<'l>,
    uparams : LevelsPtr<'l>,
    type_ : ExprPtr<'l>,
    /*safe_only : Option<bool>,*/ 
    live : &mut Live<'l, 'e>
) {
    let mut tc = live.as_tc(Some(uparams), None);
    check_vitals_w_tc(name, uparams, type_, &mut tc);
}    