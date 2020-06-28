use crate::name::{ NamePtr, NamesPtr, StringPtr };
use crate::level::LevelsPtr;
use crate::expr::ExprPtr;
use crate::tc::infer::InferFlag::*;
use crate::quot::add_quot;
use crate::inductive::IndBlock;
use crate::trace::IsTracer;
use crate::trace::steps::*;
use crate::utils::{ 
    Tc, 
    IsTc,
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

    pub fn compile_and_check(
        self,
        ctx : &mut Live<'l, 'e, impl 'e + IsTracer>
    ) {
        match self {
            AxiomSpec { name, uparams, type_, is_unsafe } => {
                let d = <DeclarPtr>::new_axiom(name, uparams, type_, is_unsafe, ctx);
                check_vitals(
                    d.name(ctx), 
                    d.uparams(ctx), 
                    d.type_(ctx), 
                    ctx
                );
                ctx.admit_declar(d);
            },
            DefinitionSpec { name, uparams, type_, val, is_unsafe } if !is_unsafe => {
                let d = <DeclarPtr>::new_definition(name, uparams, type_, val, is_unsafe, ctx);
                let val_ = match d.read(ctx) {
                    Definition { val, .. } => val,
                    _ => unreachable!()
                };
                {
                    let mut tc = ctx.as_tc(Some(uparams), None);
                    check_vitals_w_tc(d.name(&tc), d.uparams(&tc), d.type_(&tc), &mut tc);
                    let (val_type, h1) = val_.infer(Check, &mut tc);
                    val_type.assert_def_eq(d.type_(&tc), &mut tc);
                }

                ctx.admit_declar(d);
            },
            DefinitionSpec { .. } => {
           // DefinitionSpec { name, uparams, type_, val, is_unsafe } => {
                unimplemented!()
            },
           // TheoremSpec { name, uparams, type_, val } => {
            TheoremSpec { ..} => {
                unimplemented!()
            },
            OpaqueSpec {..} => {
           // OpaqueSpec { name, uparams, type_, val } => {
                unimplemented!()
            },
            QuotSpec => {
                add_quot(ctx);
            },
            InductiveSpec(mut indblock) => {
                indblock.declare_ind_types(ctx);
                indblock.declare_cnstrs(ctx);
                indblock.mk_elim_level(ctx);
                indblock.init_k_target(ctx);
                indblock.mk_local_indices(ctx);
                indblock.mk_majors_wrapper(ctx);
                indblock.mk_motives_wrapper(ctx);
                indblock.mk_minors_wrapper(ctx);
                indblock.declare_rec_rules(ctx);
                indblock.declare_recursors(ctx);                 
            },
        }
    }
       
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecRule<'a> {
    pub ctor_name : NamePtr<'a>,
    pub num_fields : u16,
    pub val : ExprPtr<'a>
}

impl<'a> RecRule<'a> {
    pub fn new(ctor_name : NamePtr<'a>, num_fields : u16, val : ExprPtr<'a>) -> Self {
        RecRule {
            ctor_name,
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
            ctor_name : self.ctor_name.insert_env(env, live),
            num_fields : self.num_fields,
            val : self.val.insert_env(env, live)
        }.alloc(env)
    }
}



impl<'a> HasNanodaDbg<'a> for RecRule<'a> {
    fn nanoda_dbg(self, ctx : &impl IsCtx<'a>) -> String {
        format!("RecRule( ctor_name : {}, num_fields : {}, val : {})", 
        self.ctor_name.nanoda_dbg(ctx), 
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
        all_ctor_names : NamesPtr<'a>,
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
        rec_rules : RecRulesPtr<'a>,
        is_k : bool,
        is_unsafe : bool,
    }
}




impl<'a> RecRulesPtr<'a> {
    pub fn get_rec_rule_aux(
        self,
        major_name : NamePtr<'a>,
        ctx : &mut impl IsCtx<'a>
    ) -> Option<(RecRulePtr<'a>, Step<GetRecRuleAuxZst>)> {
        match self.read(ctx) {
            Nil => None,
            Cons(hd, tl) if hd.read(ctx).ctor_name == major_name => {
                Some(GetRecRuleAux::Base {
                    major_name,
                    num_fields : hd.read(ctx).num_fields,
                    val : hd.read(ctx).val,
                    tl,
                    ind_arg1 : self,
                    ind_arg3 : hd
                }.step(ctx))
            },
            Cons(x, tl) => {
                let (out_rule, h1) = tl.get_rec_rule_aux(major_name, ctx)?;
                Some(GetRecRuleAux::Step{
                    ctor_name : x.read(ctx).ctor_name,
                    num_fields : x.read(ctx).num_fields,
                    val : x.read(ctx).val,
                    major_name,
                    rest : tl,
                    out_rule,
                    h1,
                    ind_arg1 : self,
                }.step(ctx))
            }

        }
    }

    pub fn get_rec_rule(
        self, 
        major : ExprPtr<'a>, 
        ctx : &mut impl IsLiveCtx<'a>
    ) -> Option<(RecRulePtr<'a>, Step<GetRecRuleZst>)> {
        let ((major_fun, major_args), h1) = major.unfold_apps(ctx);
        let (major_name, major_levels) = major_fun.try_const_info(ctx)?;
        let (rule, h2) = self.get_rec_rule_aux(major_name, ctx)?;
        Some(GetRecRule::ByAux {
            major,
            major_name,
            major_levels,
            major_args,
            rrs : self,
            rule,
            h1,
            h2,
        }.step(ctx))
    }    
}


impl<'a> DeclarPtr<'a> {
    pub fn get_hint(self, ctx : &impl IsCtx<'a>) -> ReducibilityHint {
        match self.read(ctx) {
            Definition { hint, .. } => hint,
            owise => unreachable!("Only Definition declars have a reducibility hint! found {:#?}", owise)
        }
    }

    pub fn rec_all_names(&self, ctx : &impl IsCtx<'a>) -> Option<NamesPtr<'a>> {
        match self.read(ctx) {
            Recursor { all_names, .. } => Some(all_names),
            _ => None
        }
    }

    pub fn rec_num_params(&self, ctx : &impl IsCtx<'a>) -> Option<u16> {
        match self.read(ctx) {
            Recursor { num_params, .. } => Some(num_params),
            _ => None
        }
    }

    
    pub fn rec_num_indices(&self, ctx : &impl IsCtx<'a>) -> Option<u16> {
        match self.read(ctx) {
            Recursor { num_indices, .. } => Some(num_indices),
            _ => None
        }
    }

    pub fn rec_num_motives(&self, ctx : &impl IsCtx<'a>) -> Option<u16> {
        match self.read(ctx) {
            Recursor { num_motives, .. } => Some(num_motives),
            _ => None
        }
    }

    pub fn rec_num_minors(&self, ctx : &impl IsCtx<'a>) -> Option<u16> {
        match self.read(ctx) {
            Recursor { num_minors, .. } => Some(num_minors),
            _ => None
        }
    }

    pub fn rec_major_idx(&self, ctx : &impl IsCtx<'a>) -> Option<u16> {
        match self.read(ctx) {
            Recursor { major_idx, .. } => Some(major_idx),
            _ => None
        }
    }
    
    pub fn rec_rules(&self, ctx : &impl IsCtx<'a>) -> Option<RecRulesPtr<'a>> {
        match self.read(ctx) {
            Recursor { rec_rules, .. } => Some(rec_rules),
            _ => None
        }
    }

    pub fn rec_is_k(&self, ctx : &impl IsCtx<'a>) -> Option<bool> {
        match self.read(ctx) {
            Recursor { is_k, .. } => Some(is_k),
            _ => None
        }
    }

    pub fn name(&self, ctx : &impl IsCtx<'a>) -> NamePtr<'a> {
        match self.read(ctx) {
            | Axiom       { name, .. }
            | Definition  { name, .. }
            | Theorem     { name, .. }
            | Opaque      { name, .. }
            | Quot        { name, .. }
            | Inductive   { name, .. }
            | Constructor { name, .. }
            | Recursor    { name, .. } => name,
        }
    }

    pub fn uparams(&self, ctx : &impl IsCtx<'a>) -> LevelsPtr<'a> {
        match self.read(ctx) {
            | Axiom       { uparams, .. }
            | Definition  { uparams, .. }
            | Theorem     { uparams, .. }
            | Opaque      { uparams, .. }
            | Quot        { uparams, .. }
            | Inductive   { uparams, .. }
            | Constructor { uparams, .. }
            | Recursor    { uparams, .. } => uparams,
        }
    }

    pub fn type_(&self, ctx : &impl IsCtx<'a>) -> ExprPtr<'a> {
        match self.read(ctx) {
            | Axiom       { type_, .. }
            | Definition  { type_, .. }
            | Theorem     { type_, .. }
            | Opaque      { type_, .. }
            | Quot        { type_, .. }
            | Inductive   { type_, .. }
            | Constructor { type_, .. } 
            | Recursor    { type_, .. } => type_,
        }
    }

    pub fn is_unsafe(&self, ctx : &impl IsCtx<'a>) -> bool {
        match self.read(ctx) {
            Theorem  {..}
            | Opaque {..}
            | Quot   {..} => false,
            | Axiom       { is_unsafe, .. }
            | Definition  { is_unsafe, .. }
            | Inductive   { is_unsafe, .. }
            | Constructor { is_unsafe, .. }
            | Recursor    { is_unsafe, .. } => is_unsafe,
        }
    }
    
    pub fn new_axiom<'e>(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e, impl 'e + IsTracer>,
    ) -> Self {
        Axiom {
            name,
            uparams,
            type_,
            is_unsafe,
        }.alloc(ctx)
    }

    
    pub fn new_definition<'e>(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        val : ExprPtr<'a>,
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e, impl 'e + IsTracer>,
    ) -> Self {
        let (height, h1) = val.calc_height(ctx);

        Definition {
            name,
            uparams,
            type_,
            val,
            hint : Reg(height),
            is_unsafe,
        }.alloc(ctx)
    }

    pub fn new_inductive<'e>(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        num_params : u16,
        all_ind_names : NamesPtr<'a>,
        all_ctor_names : NamesPtr<'a>,
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e, impl 'e + IsTracer>,
    ) -> Self {
        Inductive {
            name,
            uparams,
            type_,
            num_params,
            all_ind_names,
            all_ctor_names,
            is_unsafe
        }.alloc(ctx)
    }    

    pub fn new_cnstr<'e>(
        name : NamePtr<'a>,
        uparams : LevelsPtr<'a>,
        type_ : ExprPtr<'a>,
        parent_name : NamePtr<'a>,
        minor_idx : u16,
        num_params : u16,
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e, impl 'e + IsTracer>
    ) -> Self {
        Constructor {
            name,
            uparams,
            type_,
            parent_name,
            num_fields : type_.telescope_size(ctx).0 - num_params,
            minor_idx,
            num_params,
            is_unsafe
        }.alloc(ctx)
    }      

    pub fn new_recursor<'e>(
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
        is_unsafe : bool,
        ctx : &mut Live<'a, 'e, impl 'e + IsTracer>
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
        }.alloc(ctx)
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
            Inductive { num_params, all_ind_names, all_ctor_names, is_unsafe, .. } => {
                Inductive {
                    name,
                    uparams,
                    type_,
                    num_params,
                    all_ind_names : all_ind_names.insert_env(env, live),
                    all_ctor_names : all_ctor_names.insert_env(env, live),
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

pub fn check_vitals_w_tc<'t, 'l : 't, 'e : 'l>(
    name : NamePtr<'l>,
    uparams : LevelsPtr<'l>,
    type_ : ExprPtr<'l>,
    tc : &mut impl IsTc<'t, 'l, 'e>
) -> Step<CheckVitalsZst> {
    assert!(name.in_env());
    assert!(uparams.in_env());
    assert!(type_.in_env());
    assert!(!type_.has_locals(tc));
    let (b1, h1) = uparams.no_dupes(tc);
    assert!(b1);
    let (inferred, h2) = type_.infer(Check, tc);
    let (_, h3) = inferred.ensure_sort(tc);

    CheckVitals::Base {
        n : name,
        ups : uparams,
        t : type_,
        h1,
        h2,
        h3,
    }.step_only(tc)
}

pub fn check_vitals<'t, 'l : 't, 'e : 'l>(
    name : NamePtr<'l>,
    uparams : LevelsPtr<'l>,
    type_ : ExprPtr<'l>,
    /*safe_only : Option<bool>,*/ 
    live : &mut Live<'l, 'e, impl 'e + IsTracer>
) -> Step<CheckVitalsZst> {
    let mut tc = live.as_tc(Some(uparams), None);
    check_vitals_w_tc(name, uparams, type_, &mut tc)
}    