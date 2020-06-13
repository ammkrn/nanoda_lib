use crate::utils::{ IsCtx, List::*, Live };
use crate::name::{ NamePtr, NamesPtr, Name} ;
use crate::level::{ LevelPtr, LevelsPtr, Level };
use crate::expr::{ ExprPtr, ExprsPtr, Expr, Expr::*, BinderStyle::* };
use crate::env::{ Declar, RecRule, RecRulePtr, RecRulesPtr }; 
use crate::tc::infer::InferFlag::*;
use crate::name;

#[derive(Debug)]
pub struct IndBlock<'a> {
    uparams : LevelsPtr<'a>,
    num_params : u16,
    nums_indices : Vec<u16>,
    pub ind_names : NamesPtr<'a>,
    ind_types : ExprsPtr<'a>,
    nums_cnstrs : Vec<u16>,
    cnstr_names : NamesPtr<'a>,
    cnstr_types : ExprsPtr<'a>,
    is_unsafe : bool,

    local_params    : Option<ExprsPtr<'a>>,
    local_indices   : Option<ExprsPtr<'a>>,
    ind_consts      : Option<ExprsPtr<'a>>,
    block_codom     : Option<LevelPtr<'a>>,
    use_dep_elim    : Option<bool>,
    is_nonzero      : Option<bool>,

    elim_level : Option<LevelPtr<'a>>,
    k_target : Option<bool>,
    majors : Option<ExprsPtr<'a>>,
    motives : Option<ExprsPtr<'a>>,
    minors : Option<ExprsPtr<'a>>,
    rec_rules : Option<RecRulesPtr<'a>>,
}

impl<'a> IndBlock<'a> {
    fn block_codom(&self) -> LevelPtr<'a> {
        self.block_codom.expect("Block codom has not been set yet!")
    }

    fn local_params(&self) -> ExprsPtr<'a> {
        self.local_params.expect("Block local params have not been set yet!")
    }


    fn local_indices(&self) -> ExprsPtr<'a> {
        self.local_indices.expect("Local rec indices have not been set yet!")
    }

    fn ind_consts(&self) -> ExprsPtr<'a> {
        self.ind_consts.expect("ind_consts have not been set yet!")
    }

    fn use_dep_elim(&self) -> bool {
        self.use_dep_elim.expect("use_dep_elim has not been set yet!")
    }

    fn is_nonzero(&self) -> bool {
        self.is_nonzero.expect("is_nonzero has not been set yet!")
    }

    fn elim_level(&self) -> LevelPtr<'a> {
        self.elim_level.expect("elim_level has not been set yet!")
    }
    
    fn k_target(&self) -> bool {
        self.k_target.expect("k_target has not been set yet!")
    }

    fn majors(&self) -> ExprsPtr<'a> {
        self.majors.expect("majors has not been set yet!")
    }

    fn motives(&self) -> ExprsPtr<'a> {
        self.motives.expect("motives has not been set yet!")
    }

    fn minors(&self) -> ExprsPtr<'a> {
        self.minors.expect("minors has not been set yet!")
    }

    fn rec_rules(&self) -> RecRulesPtr<'a> {
        self.rec_rules.expect("rec_rules has not been set yet!")
    }
    

    pub fn new(num_params : u16,
               nums_indices : Vec<u16>,
               uparams : LevelsPtr<'a>,
               ind_names : NamesPtr<'a>,
               ind_types : ExprsPtr<'a>,
               nums_cnstrs : Vec<u16>,
               cnstr_names : NamesPtr<'a>,
               cnstr_types : ExprsPtr<'a>,
               is_unsafe : bool,
               ctx : &mut impl IsCtx<'a>) -> Self {
        assert_eq!(*&nums_cnstrs[0] as usize, cnstr_names.len(ctx).0);
        IndBlock {
            num_params,
            nums_indices,
            uparams,
            ind_names,
            ind_types,
            nums_cnstrs,
            cnstr_names,
            cnstr_types,
            is_unsafe,
            local_params : None,
            local_indices : None,
            ind_consts : None,
            block_codom : None,
            use_dep_elim : None,
            is_nonzero : None,
            elim_level : None,
            k_target : None,
            majors  : None,
            motives : None,
            minors  : None,
            rec_rules : None,
        }
    }
}
