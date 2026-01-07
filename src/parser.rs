use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecursorData, ReducibilityHint,
};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, BigUintPtr, Config, DagMarker, ExprPtr, FxHashMap, FxIndexMap,
    LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
};
use num_bigint::BigUint;
use serde::{ Deserialize, Deserializer };
use serde::de::{Error as DeError, Visitor};
use std::error::Error;
use std::io::BufRead;
use std::sync::{atomic::AtomicBool, Arc};
use std::borrow::Cow;
use std::fmt;


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Semver(u16, u16, u16);

pub(crate) const MIN_SUPPORTED_SEMVER: Semver = Semver(3, 0, 0);

pub(crate) fn parse_semver(line: &str) -> Result<Semver, Box<dyn Error>> {
    let mut iter = line.trim().split('.');

    let major = iter.next().unwrap().parse::<u16>()?;
    let minor = iter.next().unwrap().parse::<u16>()?;
    let patch = iter.next().unwrap().parse::<u16>()?;
    if iter.next().is_some() {
        Err(Box::<dyn Error>::from("improper semver line; pre-release identiiers or trailing items are not allowed"))
    } else {
        Ok(Semver(major, minor, patch))
    }
}

pub struct Parser<'a, R: BufRead> {
    buf_reader: R,
    line_num: usize,
    dag: LeanDag<'a>,
    declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct ExportJsonObject<'a> {
    #[serde(flatten)]
    val: ExportJsonVal<'a>,
    i: Option<u32>
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct RecursorRule {
    ctor: u32,
    nfields: u16,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum ExportJsonVal<'a> {
    // The exporter metadata
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr {
        pre: u32,
        str: Cow<'a, str>
    },
    #[serde(rename = "num")]
    NameNum {
        pre: u32,
        i: u32
    },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(rename = "natVal", deserialize_with = "deserialize_biguint_from_string")]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData {
        expr: u32,
        data: serde_json::Value
    },
    #[serde(rename = "letE")]
    ExprLet {
        #[serde(rename = "declName")]
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool
    },
    #[serde(rename = "const")]
    ExprConst {
        #[serde(rename = "declName")]
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32 
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "binderName")]
        binder_name: u32,
        #[serde(rename = "binderType")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle

    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "binderName")]
        binder_name: u32,
        #[serde(rename = "binderType")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: usize,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort {
        #[serde(rename = "u")]
        level: u32
    },
    #[serde(rename = "bvar")]
    ExprBVar {
        #[serde(rename = "deBruijnIndex")]
        dbj_idx: u16
    },
    #[serde(rename = "axiomInfo")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool
    },
    #[serde(rename = "thmInfo")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "defnInfo")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety
    },
    #[serde(rename = "opaqueInfo")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "inductInfo")]
    Inductive {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        all: Vec<u32>,
        ctors: Vec<u32>,
        #[serde(rename = "isRec")]
        is_rec: bool,
        #[serde(rename = "isReflexive")]
        is_reflexive: bool,
        #[serde(rename = "numIndices")]
        num_indices: u16,
        #[serde(rename = "numNested")]
        num_nested: u16,
        #[serde(rename = "numParams")]
        num_params: u16,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool

    },
    #[serde(rename = "quotInfo")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind
    },
    #[serde(rename = "ctorInfo")]
    Constructor {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
        cidx: u16,
        #[serde(rename = "numParams")]
        num_params: u16,
        #[serde(rename = "numFields")]
        num_fields: u16,
        induct: u32
    },
    #[serde(rename = "recInfo")]
    Recursor {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
        #[serde(rename = "numParams")]
        num_params: u16,
        #[serde(rename = "numIndices")]
        num_indices: u16,
        #[serde(rename = "numMotives")]
        num_motives: u16,
        #[serde(rename = "numMinors")]
        num_minors: u16,
        rules: Vec<RecursorRule>,
        all: Vec<u32>,
        k: bool,
    }
}

pub(crate) fn parse_export_file<'p, R: BufRead>(
    buf_reader: R,
    config: Config,

) -> Result<crate::util::ExportFile<'p>, Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config);
    let mut line_buffer = String::new();

    loop {
        let amt = parser.buf_reader.read_line(&mut line_buffer)?;
        if amt == 0 {
            break
        }
        parser.go1(line_buffer.as_str())?;
        parser.line_num += 1;
        line_buffer.clear();
    }
    
    let name_cache = parser.dag.mk_name_cache();
    let mut f = crate::util::ExportFile {
        dag: parser.dag,
        declars: parser.declars,
        notations: parser.notations,
        quot_checked: AtomicBool::new(false),
        name_cache,
        config: parser.config,
    };
    f.check_no_cycles();
    Ok(f)
}

impl<'a, R: BufRead> Parser<'a, R> {
    pub fn new(buf_reader: R, config: Config) -> Self {
        Self {
            buf_reader,
            line_num: 0usize,
            dag: LeanDag::new_parser(),
            declars: new_fx_index_map(),
            notations: new_fx_hash_map(),
            config,
        }
    }
    
    fn num_loose_bvars(&self, e: ExprPtr<'a>) -> u16 {
        self.dag.exprs.get_index(e.idx as usize).unwrap().num_loose_bvars()
    }

    fn has_fvars(&self, e: ExprPtr<'a>) -> bool { self.dag.exprs.get_index(e.idx as usize).unwrap().has_fvars() }

    fn get_name_ptr(&self, idx: u32) -> NamePtr<'a> {
        let out = crate::util::Ptr { idx, dag_marker: DagMarker::ExportFile, ph: std::marker::PhantomData };
        assert!((idx as usize) < self.dag.names.len());
        out
    }

    fn get_level_ptr(&self, idx: u32) -> LevelPtr<'a> {
        let out = crate::util::Ptr { idx, dag_marker: DagMarker::ExportFile, ph: std::marker::PhantomData };
        assert!((idx as usize) < self.dag.levels.len());
        out
    }
    fn get_names(&self, idxs: &[u32]) -> Vec<NamePtr<'a>> {
        let mut names = Vec::new();
        for idx in idxs.iter().copied() {
            names.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
        }
        names
    }

    fn get_uparams_ptr(&mut self, name_idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for name_idx in name_idxs.iter().copied() {
            let name_ptr = self.get_name_ptr(name_idx);
            let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
            // Has to already exist
            let idx = self.dag.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap();
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_levels_ptr(&mut self, idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for idx in idxs.iter().copied() {
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        let out = crate::util::Ptr { idx, dag_marker: DagMarker::ExportFile, ph: std::marker::PhantomData };
        assert!((idx as usize) < self.dag.exprs.len());
        out
    }

    // Used for the axiom whitelist feature.
    fn name_to_string(&self, n: NamePtr<'a>) -> String {
        match self.dag.names.get_index(n.idx()).copied().unwrap() {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + self.dag.strings.get_index(sfx.idx()).unwrap()
            }
            Name::Num(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + format!("{}", sfx).as_str()
            }
        }
    }

    fn go1(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        use ExportJsonVal::*;
        let ExportJsonObject {val, i: assigned_idx} = serde_json::from_str::<ExportJsonObject>(line).unwrap();
        match val {
            Metadata(json_val) => {
                let semver = parse_semver(&json_val.exporter.version)?;
                if semver < MIN_SUPPORTED_SEMVER {
                    return Err(Box::from(format!(
                        "parsed exporter semver is less than the minimum supported export version. Found {:?}, min supported is {:?}",
                        semver, MIN_SUPPORTED_SEMVER
                    )))
                }
            }
            NameStr {pre, str} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = StringPtr::from(
                    DagMarker::ExportFile, 
                    self.dag.strings.insert_full(std::borrow::Cow::Owned(str.to_string())).0
                );

                let insert_result = {
                    let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Str(pfx, sfx, hash))
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            NameNum {pre, i} => {
                let pfx = self.get_name_ptr(pre);
                let sfx = i as u64;
                let insert_result = {
                    let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
                    self.dag.names.insert_full(Name::Num(pfx, sfx, hash))
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            NatLit(big_uint) => {
                let num_ptr = BigUintPtr::from(DagMarker::ExportFile, self.dag.bignums.insert_full(big_uint).0);
                let insert_result = {
                    let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
                    self.dag.exprs.insert_full(Expr::NatLit { ptr: num_ptr, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            StrLit(cow_str) => {
                let s = cow_str.to_string();
                let string_ptr = StringPtr::from(
                    DagMarker::ExportFile,
                    self.dag.strings.insert_full(crate::util::CowStr::Owned(s)).0
                );
                let insert_result = {
                    let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
                    self.dag.exprs.insert_full(Expr::StringLit { ptr: string_ptr, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            LevelSucc(l) => {
                let l = self.get_level_ptr(l);
                let insert_result = {
                    let hash = hash64!(crate::level::SUCC_HASH, l);
                    self.dag.levels.insert_full(Level::Succ(l, hash))
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            LevelMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::MAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::Max(l, r, hash))
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            LevelIMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                let insert_result = {
                    let hash = hash64!(crate::level::IMAX_HASH, l, r);
                    self.dag.levels.insert_full(Level::IMax(l, r, hash))
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            LevelParam(var_idx) => {
                 let n = self.get_name_ptr(var_idx);
                 let insert_result = {
                     let hash = hash64!(crate::level::PARAM_HASH, n);
                     self.dag.levels.insert_full(Level::Param(n, hash))
                 };
                 assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprSort {level} => {
                let level = self.get_level_ptr(level);
                let insert_result = {
                    let hash = hash64!(crate::expr::SORT_HASH, level);
                    self.dag.exprs.insert_full(Expr::Sort { level, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprMData {..} => {
                panic!("Expr.mdata not supported");
            }
            ExprConst {name, levels} => {
                let name = self.get_name_ptr(name);
                let levels = self.get_levels_ptr(&levels);
                let insert_result = {
                    let hash = hash64!(crate::expr::CONST_HASH, name, levels);
                    self.dag.exprs.insert_full(Expr::Const { name, levels, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprApp {fun, arg} => {
                let fun = self.get_expr_ptr(fun);
                let arg = self.get_expr_ptr(arg);
                let insert_result = {
                    let hash = hash64!(crate::expr::APP_HASH, fun, arg);
                    let num_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
                    let locals = self.has_fvars(fun) || self.has_fvars(arg);
                    self.dag.exprs.insert_full(Expr::App { fun, arg, num_loose_bvars: num_bvars, has_fvars: locals, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprBVar {dbj_idx} => {
                let insert_result = {
                    let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
                    self.dag.exprs.insert_full(Expr::Var { dbj_idx, hash })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }

            ExprLambda {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, binder_type, body);
                    let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Lambda {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprPi {binder_name, binder_type, binder_info, body} => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, binder_type, body);
                    let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Pi {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprLet {name, ty, value, body, nondep} => {
                let binder_name = self.get_name_ptr(name);
                let binder_type = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let body = self.get_expr_ptr(body);
                let insert_result = {
                    let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
                    let num_bvars = self
                        .num_loose_bvars(binder_type)
                        .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
                    let locals = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
                    self.dag.exprs.insert_full(Expr::Let {
                        binder_name,
                        binder_type,
                        val,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                        nondep
                    })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            ExprProj {type_name, idx, structure: struct_} => {
                let ty_name = self.get_name_ptr(type_name);
                let structure = self.get_expr_ptr(struct_);
                let insert_result = {
                    let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
                    let num_bvars = self.num_loose_bvars(structure);
                    let locals = self.has_fvars(structure);
                    self.dag.exprs.insert_full(Expr::Proj {
                        ty_name,
                        idx,
                        structure,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    })
                };
                assert_eq!((assigned_idx.unwrap() as usize, true), insert_result);
            }
            Axiom {name, ty, uparams, is_unsafe} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let info = DeclarInfo { name, ty, uparams };
                let axiom = Declar::Axiom { info };
                let axiom_permitted = self.config.permitted_axioms.contains(&self.name_to_string(name));
                if !axiom_permitted && self.config.unpermitted_axiom_hard_error {
                    panic!("export file declares unpermitted axiom {:?}", self.name_to_string(name))
                }
                if axiom_permitted {
                    self.declars.insert(name, axiom);
                }
            }
            Defn {name, ty, uparams, value, hint, safety} => {
                assert!(!matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial));
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Definition { info, val, hint };
                self.declars.insert(name, definition);
            }
            Thm {name, ty, uparams, value} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let theorem = Declar::Theorem { info, val };
                self.declars.insert(name, theorem);
            }
            Opaque {name, ty, uparams, value} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Opaque { info, val };
                self.declars.insert(name, definition);
            }
            Quot {name, ty, uparams, ..} => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let quot = Declar::Quot { info };
                self.declars.insert(name, quot);
            }
            Constructor {name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, ..} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let parent_inductive = self.get_name_ptr(induct);
                let ctor_idx = cidx;
                let ctor = Declar::Constructor(ConstructorData {
                    info,
                    inductive_name: parent_inductive,
                    ctor_idx,
                    num_params,
                    num_fields,
                });
                self.declars.insert(name, ctor);
            }
            Recursor {name, uparams, ty, rules, is_unsafe, num_params, num_indices, num_motives, num_minors, k, all, ..} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let rules = rules.into_iter().map(|RecursorRule {rhs, ctor, nfields}| 
                    crate::env::RecRule {
                        val: self.get_expr_ptr(rhs),
                        ctor_name: self.get_name_ptr(ctor),
                        ctor_telescope_size_wo_params: nfields
                    }
                ).collect::<Vec<_>>();
                let all_inductives = self.get_names(&all);
                let recursor = Declar::Recursor(RecursorData {
                    info,
                    all_inductives: Arc::from(all_inductives),
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rec_rules: Arc::from(rules),
                    is_k: k,
                });
                self.declars.insert(name, recursor);
            }
            Inductive {name, ty, uparams, all, ctors, is_rec, num_nested, num_params, num_indices, is_unsafe, ..} => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let all_ind_names =  Arc::from(self.get_names(&all)); 
                let all_ctor_names = Arc::from(self.get_names(&ctors)); 
                let inductive = Declar::Inductive(InductiveData {
                    info: DeclarInfo { name, uparams, ty },
                    is_recursive: is_rec,
                    is_nested: num_nested > 0,
                    num_params,
                    num_indices,
                    all_ind_names,
                    all_ctor_names,
                });
                self.declars.insert(name, inductive);
            }
        }
        Ok(())
    }
}

fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where D: Deserializer<'de> {
    use std::str::FromStr;
    struct BigUintStringVisitor;

    impl<'de> Visitor<'de> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E> where E: DeError {
            BigUint::from_str(v).map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E> where E: DeError {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}