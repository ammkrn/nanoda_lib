use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecRule, RecursorData, ReducibilityHint,
    ReducibilityHint::*,
};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, BigUintPtr, Config, DagMarker, ExportFile, ExprPtr, FxHashMap, FxIndexMap,
    LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
};
use num_bigint::BigUint;
use std::error::Error;
use std::io::BufRead;
use std::str::{FromStr, SplitWhitespace};
use std::sync::{atomic::AtomicBool, Arc};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Semver(u16, u16, u16);

pub(crate) const MIN_SUPPORTED_SEMVER: Semver = Semver(2, 0, 0);

pub struct Parser<'a, R: BufRead> {
    buf_reader: R,
    line_num: usize,
    dag: LeanDag<'a>,
    // rec rules are treated separately during parsing because the export
    // file doesn't nest them within a recursor, but they're not stored separately
    // in the dag, so we need to hold onto them temporarily in a way that can be
    // indexed by a usize.
    rec_rules: Vec<RecRule<'a>>,
    declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
}

pub(crate) fn parse_export_file<'p, R: BufRead>(
    buf_reader: R,
    config: Config,
) -> Result<ExportFile<'p>, Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config);
    // A temporary buffer to hold the line being parsed; gets filled and cleared in each loop,
    // but lets us use std's `SplitWhitespace`, which makes life easier.
    let mut line_buffer = String::new();
    let semver = {
        parser.buf_reader.read_line(&mut line_buffer)?;
        parse_semver(&line_buffer)?
    };
    if semver < MIN_SUPPORTED_SEMVER {
        return Err(Box::from(format!(
            "parsed semver is less than the minimum supported export version. Found {:?}, min supported is {:?}",
            semver, MIN_SUPPORTED_SEMVER
        )))
    }
    loop {
        // Make sure the line buffer is empty.
        line_buffer.clear();
        match parser.buf_reader.read_line(&mut line_buffer)? {
            // If EOF has been reached, we're done.
            0 => break,
            // If we're able to read more than 0 bytes, a line has been parsed.
            _ => {
                let mut line_rem_toks = line_buffer.split_whitespace();
                let tok = line_rem_toks
                    .next()
                    .ok_or_else(|| Box::<dyn Error>::from("Export file cannot contain empty lines"))?;
                match tok {
                    s @ "#PREFIX" | s @ "#INFIX" | s @ "#POSTFIX" => parser.parse_notation(s, &mut line_rem_toks),
                    "#AX" => parser.parse_axiom(&mut line_rem_toks),
                    "#DEF" => parser.parse_def(&mut line_rem_toks),
                    "#OPAQ" => parser.parse_opaque(&mut line_rem_toks),
                    "#QUOT" => parser.parse_quot(&mut line_rem_toks),
                    "#THM" => parser.parse_theorem(&mut line_rem_toks),
                    "#IND" => parser.parse_inductive(&mut line_rem_toks),
                    "#CTOR" => parser.parse_constructor(&mut line_rem_toks),
                    "#REC" => parser.parse_recursor(&mut line_rem_toks),
                    // otherwise, the parsed line is some non-declaration primitive
                    // (Name, Level, Expr) which should be prefixed by its index.
                    leading_idx => 
                      match parser.parse_primitive(leading_idx.parse::<u32>()?, &mut line_rem_toks) {
                        Ok(_) => (),
                        Err(e) => {
                            return Err(Box::<dyn Error>::from(
                                format!("line buffer := {}\n\n err := {}", line_buffer, e)
                            ))
                        }
                      }
                }
            }
        }
        // Increment the line number; this is only tracked for error reporting.
        parser.line_num += 1;
    }

    let name_cache = parser.dag.mk_name_cache();
    let mut f = ExportFile {
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
            rec_rules: Vec::new(),
            declars: new_fx_index_map(),
            notations: new_fx_hash_map(),
            config,
        }
    }

    fn parse_rest_cowstr(&self, ws: &mut SplitWhitespace) -> Result<crate::util::CowStr<'a>, Box<dyn Error>> {
        let mut s = String::new();
        for x in ws {
            s.push_str(x);
            s.push(' ');
        }
        if s.ends_with(" ") {
            s.pop();
        }
        Ok(std::borrow::Cow::Owned(s.to_owned()))
        //match ws.next() {
        //    None => Ok(std::borrow::Cow::Owned(s.to_owned())),
        //    Some(ss) => {
        //      return Err(Box::<dyn Error>::from(
        //          format!("Expected iterator to end, got {}", ss)
        //      ))
        //    }
        //}
    }

    /// Allocate a parsed string as a DAG item.
    fn parse_insert_string(&mut self, ws: &mut SplitWhitespace) -> Result<StringPtr<'a>, Box<dyn Error>> {
        let s = self.parse_rest_cowstr(ws)?;
        Ok(StringPtr::from(DagMarker::ExportFile, self.dag.strings.insert_full(s).0))
    }

    /// Parse a `#NS` row and add it to the dag. The leading index and discriminator
    /// have already been found, and the leading index is passed as `idx`.
    fn parse_name_str_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) -> Result<(), Box<dyn Error>> {
        let pfx = self.parse_name_ptr(ws);
        let sfx = self.parse_insert_string(ws)?;
        let insert_result = {
            let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
            self.dag.names.insert_full(Name::Str(pfx, sfx, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
        Ok(())
    }

    /// Parse a `#NI` row and add it to the dag. The leading index and discriminator
    /// have already been found, and the leading index is passed as `idx`.
    fn parse_name_num_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let pfx = self.parse_name_ptr(ws);
        let sfx = parse_u64(ws);
        let insert_result = {
            let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
            self.dag.names.insert_full(Name::Num(pfx, sfx, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_level_succ_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let l = self.parse_level_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::level::SUCC_HASH, l);
            self.dag.levels.insert_full(Level::Succ(l, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }
    fn parse_level_max_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let l = self.parse_level_ptr(ws);
        let r = self.parse_level_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::level::MAX_HASH, l, r);
            self.dag.levels.insert_full(Level::Max(l, r, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_level_imax_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let l = self.parse_level_ptr(ws);
        let r = self.parse_level_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::level::IMAX_HASH, l, r);
            self.dag.levels.insert_full(Level::IMax(l, r, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_level_param_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let n = self.parse_name_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::level::PARAM_HASH, n);
            self.dag.levels.insert_full(Level::Param(n, hash))
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn num_loose_bvars(&self, e: ExprPtr<'a>) -> u16 {
        self.dag.exprs.get_index(e.idx as usize).unwrap().num_loose_bvars()
    }

    fn has_fvars(&self, e: ExprPtr<'a>) -> bool { self.dag.exprs.get_index(e.idx as usize).unwrap().has_fvars() }

    fn parse_expr_var_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let dbj_idx = parse_u16(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
            self.dag.exprs.insert_full(Expr::Var { dbj_idx, hash })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_sort_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let level = self.parse_level_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::SORT_HASH, level);
            self.dag.exprs.insert_full(Expr::Sort { level, hash })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_const_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let levels = self.parse_level_ptrs(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::CONST_HASH, name, levels);
            self.dag.exprs.insert_full(Expr::Const { name, levels, hash })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_app_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let fun = self.parse_expr_ptr(ws);
        let arg = self.parse_expr_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::APP_HASH, fun, arg);
            let num_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
            let locals = self.has_fvars(fun) || self.has_fvars(arg);
            self.dag.exprs.insert_full(Expr::App { fun, arg, num_loose_bvars: num_bvars, has_fvars: locals, hash })
        };

        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_lambda_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let binder_style = parse_binder_info(ws);
        let binder_name = self.parse_name_ptr(ws);
        let binder_type = self.parse_expr_ptr(ws);
        let body = self.parse_expr_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
            let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
            let locals = self.has_fvars(binder_type) || self.has_fvars(body);
            self.dag.exprs.insert_full(Expr::Lambda {
                binder_name,
                binder_style,
                binder_type,
                body,
                num_loose_bvars: num_bvars,
                has_fvars: locals,
                hash,
            })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_pi_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let binder_style = parse_binder_info(ws);
        let binder_name = self.parse_name_ptr(ws);
        let binder_type = self.parse_expr_ptr(ws);
        let body = self.parse_expr_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
            let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
            let locals = self.has_fvars(binder_type) || self.has_fvars(body);
            self.dag.exprs.insert_full(Expr::Pi {
                binder_name,
                binder_style,
                binder_type,
                body,
                num_loose_bvars: num_bvars,
                has_fvars: locals,
                hash,
            })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_let_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let binder_name = self.parse_name_ptr(ws);
        let binder_type = self.parse_expr_ptr(ws);
        let val = self.parse_expr_ptr(ws);
        let body = self.parse_expr_ptr(ws);
        let insert_result = {
            let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body);
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
            })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_proj_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let ty_name = self.parse_name_ptr(ws);
        let idx = parse_usize(ws);
        let structure = self.parse_expr_ptr(ws);
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
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_stringlit_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let s = parse_hex_string(ws).unwrap();
        let string_ptr =
            StringPtr::from(DagMarker::ExportFile, self.dag.strings.insert_full(crate::util::CowStr::Owned(s)).0);
        let insert_result = {
            let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
            self.dag.exprs.insert_full(Expr::StringLit { ptr: string_ptr, hash })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_expr_natlit_row(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) {
        let chars = ws.next().unwrap();
        let bignat = BigUint::from_str(chars).unwrap();
        let num_ptr = BigUintPtr::from(DagMarker::ExportFile, self.dag.bignums.insert_full(bignat).0);
        let insert_result = {
            let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
            self.dag.exprs.insert_full(Expr::NatLit { ptr: num_ptr, hash })
        };
        assert_eq!((assigned_idx as usize, true), insert_result);
    }

    fn parse_name_ptr(&self, ws: &mut SplitWhitespace) -> NamePtr<'a> {
        let idx = parse_u32(ws);
        NamePtr::from(DagMarker::ExportFile, idx as usize)
    }

    fn try_parse_name_ptr(&self, ws: &mut SplitWhitespace) -> Option<NamePtr<'a>> {
        let idx = try_parse_u32(ws)?;
        Some(NamePtr::from(DagMarker::ExportFile, idx as usize))
    }

    fn parse_level_ptr(&self, ws: &mut SplitWhitespace) -> LevelPtr<'a> {
        let idx = parse_u32(ws);
        LevelPtr::from(DagMarker::ExportFile, idx as usize)
    }

    fn parse_expr_ptr(&self, ws: &mut SplitWhitespace) -> ExprPtr<'a> {
        let idx = parse_u32(ws);
        crate::util::Ptr { idx, dag_marker: DagMarker::ExportFile, ph: std::marker::PhantomData }
    }

    // Given a sequence of numbers [n1, n2, n3], collect the sequence
    // [levels[n1], levels[n2], levels[n3]] into a list.
    fn parse_level_ptrs(&mut self, ws: &mut SplitWhitespace) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for cs in ws {
            let i = cs.parse::<usize>().expect("uparams_char_chunk");
            levels.push(LevelPtr::from(DagMarker::ExportFile, i))
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(levels)).0)
    }

    /// Consumes the rest of the iterator.
    fn parse_names(&mut self, ws: &mut SplitWhitespace, limit: Option<u16>) -> Vec<NamePtr<'a>> {
        let mut name_ptrs = Vec::new();
        if let Some(limit) = limit {
            for _ in 0..limit {
                let char_chunk = ws.next().unwrap();
                let idx = char_chunk.parse::<u32>().expect("uparams_char_chunk");
                name_ptrs.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
            }
        } else {
            for char_chunk in ws {
                let idx = char_chunk.parse::<u32>().expect("uparams_char_chunk");
                name_ptrs.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
            }
        }
        name_ptrs
    }

    fn name_as_level(&mut self, ws: &mut SplitWhitespace) -> Option<LevelPtr<'a>> {
        let name_ptr = self.try_parse_name_ptr(ws)?;
        let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
        // Has to already exist
        let idx = self.dag.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap();
        Some(LevelPtr::from(DagMarker::ExportFile, idx))
    }

    // This doesn't interfere with the export file indices because every declaration
    // also has some associated `Expr::Const` which would already have made the
    // uparam names an associated `Level`
    /// Consumes the rest of the iterator.
    fn parse_uparams(&mut self, ws: &mut SplitWhitespace, limit: Option<u16>) -> LevelsPtr<'a> {
        let mut level_ptrs = Vec::new();
        if let Some(limit) = limit {
            for _ in 0..limit {
                level_ptrs.push(self.name_as_level(ws).unwrap())
            }
        } else {
            while let Some(level_ptr) = self.name_as_level(ws) {
                level_ptrs.push(level_ptr)
            }
        }
        LevelsPtr::from(DagMarker::ExportFile, self.dag.uparams.insert_full(Arc::from(level_ptrs)).0)
    }

    fn parse_primitive(&mut self, assigned_idx: u32, ws: &mut SplitWhitespace) -> Result<(), Box<dyn Error>> {
        let discrim = ws.next().expect("Parse primitive");
        match discrim {
            "#RR" => self.parse_rec_rule(assigned_idx, ws),
            "#NS" => self.parse_name_str_row(assigned_idx, ws)?,
            "#NI" => self.parse_name_num_row(assigned_idx, ws),
            "#US" => self.parse_level_succ_row(assigned_idx, ws),
            "#UM" => self.parse_level_max_row(assigned_idx, ws),
            "#UIM" => self.parse_level_imax_row(assigned_idx, ws),
            "#UP" => self.parse_level_param_row(assigned_idx, ws),
            "#EV" => self.parse_expr_var_row(assigned_idx, ws),
            "#ES" => self.parse_expr_sort_row(assigned_idx, ws),
            "#EC" => self.parse_expr_const_row(assigned_idx, ws),
            "#EA" => self.parse_expr_app_row(assigned_idx, ws),
            "#EL" => self.parse_expr_lambda_row(assigned_idx, ws),
            "#EP" => self.parse_expr_pi_row(assigned_idx, ws),
            "#EZ" => self.parse_expr_let_row(assigned_idx, ws),
            "#EJ" => self.parse_expr_proj_row(assigned_idx, ws),
            "#ELN" => {
                if !self.config.nat_extension {
                    return Err(Box::<dyn Error>::from(
                        "Export file contained nat literal, but nat kernel extension not enabled",
                    ))
                }
                self.parse_expr_natlit_row(assigned_idx, ws)
            }
            "#ELS" => {
                if !self.config.string_extension {
                    return Err(Box::<dyn Error>::from(
                        "Export file contained string literal, but string lit extension not enabled",
                    ))
                }
                self.parse_expr_stringlit_row(assigned_idx, ws)
            }
            owise => return Err(Box::<dyn Error>::from(format!("Unrecognized primitive {}", owise))),
        }
        Ok(())
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

    fn parse_axiom(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let uparams = self.parse_uparams(ws, None);
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

    fn parse_hint(&mut self, ws: &mut SplitWhitespace) -> ReducibilityHint {
        match ws.next() {
            Some("O") => Opaque,
            Some("A") => Abbrev,
            Some("R") => Regular(parse_u16(ws)),
            owise => panic!("expected to parse reducibility hint, found {:?}", owise),
        }
    }

    fn parse_def(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let val = self.parse_expr_ptr(ws);
        let hint = self.parse_hint(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let definition = Declar::Definition { info, val, hint };
        self.declars.insert(name, definition);
    }

    fn parse_opaque(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let val = self.parse_expr_ptr(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let definition = Declar::Opaque { info, val };
        self.declars.insert(name, definition);
    }

    pub(crate) fn parse_theorem(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let val = self.parse_expr_ptr(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let theorem = Declar::Theorem { info, val };
        self.declars.insert(name, theorem);
    }

    fn parse_quot(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let quot = Declar::Quot { info };
        self.declars.insert(name, quot);
    }

    fn parse_inductive(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let _is_reflexive = parse_nat_as_bool(ws);
        let is_recursive = parse_nat_as_bool(ws);
        let is_nested = parse_nat_as_bool(ws);
        let num_params = parse_u16(ws);
        let num_indices = parse_u16(ws);
        let num_inductives = parse_u16(ws);
        let all_ind_names = Arc::from(self.parse_names(ws, Some(num_inductives)));
        let num_ctors = parse_u16(ws);
        let all_ctor_names = Arc::from(self.parse_names(ws, Some(num_ctors)));
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };

        let inductive = Declar::Inductive(InductiveData {
            info,
            is_recursive,
            is_nested,
            num_params,
            num_indices,
            all_ind_names,
            all_ctor_names,
        });
        self.declars.insert(name, inductive);
    }

    fn parse_constructor(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let parent_inductive = self.parse_name_ptr(ws);
        let ctor_idx = parse_u16(ws);
        let num_params = parse_u16(ws);
        let num_fields = parse_u16(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let ctor = Declar::Constructor(ConstructorData {
            info,
            inductive_name: parent_inductive,
            ctor_idx,
            num_params,
            num_fields,
        });
        self.declars.insert(name, ctor);
    }

    fn parse_rec_rule(&mut self, assigned_idx: u32, line_rem_toks: &mut SplitWhitespace) {
        let ctor_name = self.parse_name_ptr(line_rem_toks);
        let ctor_telescope_size_wo_params = parse_u16(line_rem_toks);
        let val = self.parse_expr_ptr(line_rem_toks);
        let rule = RecRule { ctor_name, ctor_telescope_size_wo_params, val };
        assert_eq!(assigned_idx as usize, self.rec_rules.len());
        self.rec_rules.push(rule)
    }

    fn parse_recursor(&mut self, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let ty = self.parse_expr_ptr(ws);
        let num_inductives = parse_u16(ws);
        let all_inductives = Arc::from(self.parse_names(ws, Some(num_inductives)));

        let num_params = parse_u16(ws);
        let num_indices = parse_u16(ws);
        let num_motives = parse_u16(ws);
        let num_minors = parse_u16(ws);
        let num_rec_rules = parse_u16(ws);
        let mut rec_rules = Vec::new();
        for _ in 0..num_rec_rules {
            let idx = parse_usize(ws);
            let rr = self.rec_rules[idx];
            rec_rules.push(rr);
        }
        let is_k = parse_nat_as_bool(ws);
        let uparams = self.parse_uparams(ws, None);
        let info = DeclarInfo { name, ty, uparams };
        let recursor = Declar::Recursor(RecursorData {
            info,
            all_inductives,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            rec_rules: Arc::from(rec_rules),
            is_k,
        });
        self.declars.insert(name, recursor);
    }

    fn parse_notation(&mut self, discrim: &str, ws: &mut SplitWhitespace) {
        let name = self.parse_name_ptr(ws);
        let priority = parse_usize(ws);
        let symbol = Arc::from(ws.flat_map(|x| x.chars()).collect::<String>());
        let made = match discrim {
            "#PREFIX" => Notation::new_prefix(name, priority, symbol),
            "#INFIX" => Notation::new_infix(name, priority, symbol),
            "#POSTFIX" => Notation::new_postfix(name, priority, symbol),
            _ => unreachable!(),
        };
        self.notations.insert(name, made);
    }
}

fn parse_usize(ws: &mut SplitWhitespace) -> usize {
    ws.next().expect("parser::parse_usize::next()").parse::<usize>().expect("parser::parse_usize::and_then")
}

fn parse_nat_as_bool(ws: &mut SplitWhitespace) -> bool {
    match ws.next() {
        Some("0") => false,
        Some(s) if s.chars().all(|c| c.is_ascii_digit()) => true,
        owise => panic!("Parse bool expected 1 or 0, got {:?}", owise),
    }
}

fn parse_u64(ws: &mut SplitWhitespace) -> u64 {
    ws.next().expect("parser::parse_u64::next()").parse::<u64>().expect("parser::parse_u64::and_then")
}
fn parse_u32(ws: &mut SplitWhitespace) -> u32 {
    ws.next().expect("parser::parse_u32::next").parse::<u32>().expect("parser::parse_u32::parse")
}

fn try_parse_u32(ws: &mut SplitWhitespace) -> Option<u32> { ws.next().and_then(|s| s.parse::<u32>().ok()) }

fn parse_u16(ws: &mut SplitWhitespace) -> u16 {
    ws.next().expect("parser::parse_u16::next").parse::<u16>().expect("parser::parse_u16::parse")
}

fn parse_binder_info(ws: &mut SplitWhitespace) -> BinderStyle {
    ws.next()
        .map(|elem| match elem {
            s if s.contains("#BD") => BinderStyle::Default,
            s if s.contains("#BI") => BinderStyle::Implicit,
            s if s.contains("#BC") => BinderStyle::InstanceImplicit,
            s if s.contains("#BS") => BinderStyle::StrictImplicit,
            _ => panic!(),
        })
        .expect("parse_binder_info")
}

pub(crate) fn parse_hex_string(ws: &mut SplitWhitespace) -> Option<String> {
    let bytes = ws.map(|hex_pair| u8::from_str_radix(hex_pair, 16).ok()).collect::<Option<Vec<u8>>>()?;
    String::from_utf8(bytes).ok()
}

/// Information about the semver is currently unused awaiting community input.
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
