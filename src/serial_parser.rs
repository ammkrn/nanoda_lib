use std::str::SplitWhitespace;

use crate::name::{ Name, mk_anon };
use crate::quot::Quot;
use crate::level::{ Level, mk_imax, mk_max, mk_succ, mk_param, mk_zero };
use crate::expr::{ Expr, Binder, BinderStyle, mk_app, mk_prop, mk_sort,
                   mk_var, mk_let, mk_pi, mk_lambda, mk_const };
use crate::inductive::newinductive::{ InductiveDeclar, 
                                      InductiveType, 
                                      Constructor };
use crate::env::{ Notation,
                  ArcEnv, 
                  DefinitionVal,
                  add_axiom,
                  add_definition,
                  add_inductive,
                  add_quot };
use crate::errors::{ NanodaResult, NanodaErr::* };

pub struct LineParser {
    pub line_num: usize,
    pub names  : Vec<Name>,
    pub levels : Vec<Level>,
    pub exprs  : Vec<Expr>,
    pub env_handle : ArcEnv,
    pub prop : Expr,
}

impl LineParser {
    pub fn new(env_handle : ArcEnv) -> LineParser {
        let mut parser = LineParser {
            line_num: 1usize,
            names : Vec::with_capacity(12_000),
            levels : Vec::with_capacity(250),
            exprs : Vec::with_capacity(400_000),
            env_handle,
            prop : mk_prop(),
        };

        parser.names.push(mk_anon());
        parser.levels.push(mk_zero());
        parser
    }

    pub fn ref_anon(&self) -> Name {
        self.names[0].clone()
    }

    pub fn ref_zero(&self) -> Level {
        self.levels[0].clone()
    }

    pub fn ref_prop(&self) -> Expr {
        self.prop.clone()
    }

    pub fn parse_check_all(s : String, env_handle : ArcEnv) -> NanodaResult<()> {
        let mut parser = LineParser::new(env_handle);
        let mut as_lines = s.lines();

        while let Some(line) = &mut as_lines.next() {
            match parser.try_next(line) {
                Ok(_) => (),
                Err(e) => return Err(e)
            }

           parser.line_num  += 1;
        }

        Ok(())
    }

    pub fn try_next(&mut self, line : &str) -> NanodaResult<()> {
        let mut ws = line.split_whitespace();
        match ws.next().ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))? {
            "#AX"          => self.make_axiom(&mut ws),
            "#DEF"         => self.make_definition(&mut ws),
            "#QUOT"        => self.make_quotient(),
            "#IND"         => self.make_inductive(&mut ws),
            s @ "#INFIX"   => self.make_notation(s, line, &mut ws),
            s @ "#PREFIX"  => self.make_notation(s, line, &mut ws),
            s @ "#POSTFIX" => self.make_notation(s, line, &mut ws),
            owise1         => {
                let leading_num = owise1.parse::<usize>()
                                        .map_err(|e| ParseIntErr(self.line_num, line!(), e))?;
                let mut as_chars = ws.next()
                                     .ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))?
                                     .chars();
                assert!(as_chars.next() == Some('#')); 

                match as_chars.next() {
                    Some('N') => self.make_name(leading_num, as_chars.next().ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))?, &mut ws),
                    Some('U') => self.make_level(leading_num, as_chars.next().ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))?, &mut ws),
                    Some('E') => self.make_expr(leading_num, as_chars.next().ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))?, &mut ws),
                    _ => return Err(ParseStringErr(self.line_num, line!()))
                }
            }
        }
    }


    fn parse_usize(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<usize> {
          ws.next()
            .ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))
            .and_then(|item| item.parse::<usize>().map_err(|e| ParseIntErr(self.line_num, line!(), e)))
    }

    fn parse_u64(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<u64> {
          ws.next()
            .ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))
            .and_then(|item| item.parse::<u64>().map_err(|e| ParseIntErr(self.line_num, line!(), e)))
    }
    
    
    fn parse_rest_usize(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Vec<usize>> {
           ws.map(|elem| elem.parse::<usize>().map_err(|e| ParseIntErr(self.line_num, line!(), e)))
             .collect::<NanodaResult<Vec<usize>>>()
    }
    
    fn parse_rest_string(&mut self, ws : &mut SplitWhitespace) -> String {
        ws.collect::<String>()
    }

    pub fn get_levels(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Vec<Level>> {
          ws.into_iter()
            .map(|elem| elem.parse::<usize>().map_err(|e| ParseIntErr(self.line_num, line!(), e)))
            .map(|res| res.map(|idx| self.levels.get(idx).map(|x| x).cloned().unwrap_or_else(|| self.ref_zero())))
            .collect::<NanodaResult<Vec<Level>>>()
    }

    pub fn get_uparams(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Vec<Level>> {
          ws.into_iter()
            .map(|elem| elem.parse::<usize>().map_err(|e| ParseIntErr(self.line_num, line!(), e)))
            .map(|res| res.map(|idx| {
                let name = self.names.get(idx).cloned().unwrap_or_else(|| self.ref_anon());
                mk_param(name)
            }))
            .collect::<NanodaResult<Vec<Level>>>()
    }

    pub fn parse_binder_info(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<BinderStyle> {
        ws.next().map(|elem| match elem {
            s if s.contains("#BD") => BinderStyle::Default,
            s if s.contains("#BI") => BinderStyle::Implicit,
            s if s.contains("#BC") => BinderStyle::InstImplicit,
            s if s.contains("#BS") => BinderStyle::StrictImplicit,
            _ => unreachable!(),
        }).ok_or_else(|| ParseExhaustedErr(self.line_num, line!()))
    }

    pub fn get_name(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Name> {
        self.parse_usize(ws)
            .map(|idx| self.names.get(idx).map(|x| x).cloned().unwrap_or_else(|| self.ref_anon()))
    }


    pub fn get_level(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Level> {
        self.parse_usize(ws)
            .map(|idx| self.levels.get(idx).map(|x| x).cloned().unwrap_or_else(|| self.ref_zero()))
    }

    pub fn get_expr(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<Expr> {
        self.parse_usize(ws)
            .map(|idx| self.exprs.get(idx).map(|x| x).cloned().unwrap_or_else(|| self.ref_prop()))
    }

    pub fn make_name(&mut self, new_pos : usize, kind : char, ws : &mut SplitWhitespace) -> NanodaResult<()> {
        let prefix_name = self.get_name(ws)?;
        let new_name = match kind {
            'S' => prefix_name.extend_str(self.parse_rest_string(ws).as_str()),
            'I' => self.parse_u64(ws).map(|hd| prefix_name.extend_num(hd))?,
            _ => unreachable!("parser `make_name` line : {}", line!())
        };

        write_elem_strict(&mut self.names, new_name, new_pos)
    }


    pub fn make_level(&mut self, new_pos : usize, kind : char, ws : &mut SplitWhitespace) -> NanodaResult<()> {

        let new_level = match kind {
            'S'  => mk_succ(self.get_level(ws)?),
            'M'  => mk_max(self.get_level(ws)?, self.get_level(ws)?),
            'I'  => mk_imax(self.get_level(ws)?, self.get_level(ws)?),
            'P'  => mk_param(self.get_name(ws)?),
            _ => unreachable!("parser line : {}", line!())
        };

        write_elem_strict(&mut self.levels, new_level, new_pos)
    }


    pub fn make_expr(&mut self, new_pos : usize, kind : char, ws : &mut SplitWhitespace) -> NanodaResult<()> {

        let new_expr = match kind {
            'V' => mk_var(self.parse_usize(ws)?),
            'S' => mk_sort(self.get_level(ws)?),
            'C' => mk_const(self.get_name(ws)?, self.get_levels(ws)?),
            'A' => mk_app(self.get_expr(ws)?, self.get_expr(ws)?),
            'L' => {
                let binder_info = self.parse_binder_info(ws)?;
                let binder_name = self.get_name(ws)?;
                let domain = self.get_expr(ws)?;
                let lambda = mk_lambda(Binder::mk(binder_name, domain, binder_info), self.get_expr(ws)?);
                lambda
            },
            'P' => {
                let binder_info = self.parse_binder_info(ws)?;
                let binder_name = self.get_name(ws)?;
                let dom = self.get_expr(ws)?;
                mk_pi(Binder::mk(binder_name, dom, binder_info), self.get_expr(ws)?)
            },
            'Z' => {
                let name = self.get_name(ws)?;
                let ty = self.get_expr(ws)?;
                let val = self.get_expr(ws)?;
                let body = self.get_expr(ws)?;
                mk_let(Binder::mk(name, ty, BinderStyle::Default), val, body)
            },
            otherwise => unreachable!("parser `make_expr` line : {} expectex expression cue, got {:?}", line!(), otherwise)
        };

        write_elem_strict(&mut self.exprs, new_expr, new_pos)
    }


    pub fn make_notation(&mut self, kind : &str, line : &str, ws : &mut SplitWhitespace) -> NanodaResult<()> {
        let name = self.get_name(ws)?;
        let priority = self.parse_usize(ws)?;
        // Elegance.
        let symbol = line.chars().skip_while(|x| !x.is_whitespace())
                                 .skip(1)
                                 .skip_while(|x| !x.is_whitespace())
                                 .skip(1)
                                 .skip_while(|x| !x.is_whitespace())
                                 .skip(1)
                                 .collect::<String>();
        let made = match kind {
            "#PREFIX"  => Notation::new_prefix(name.clone(), priority, symbol),
            "#INFIX"   => Notation::new_infix(name.clone(), priority, symbol),
            "#POSTFIX" => Notation::new_postfix(name.clone(), priority, symbol),
            _ => unreachable!()
        };

        self.env_handle.write().add_notation(&name, made);
        Ok(())
    }

    pub fn make_axiom(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<()> {
        let name = self.get_name(ws)?;
        let ty = self.get_expr(ws)?;
        let uparams = self.get_uparams(ws)?;

        let new_axiom = crate::env::AxiomVal::new(name, uparams, ty, None);
        add_axiom(new_axiom, self.env_handle.clone(), true)
    }

    pub fn make_definition(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<()> {
        let name = self.get_name(ws)?;
        let ty = self.get_expr(ws)?;
        let val = self.get_expr(ws)?;

        let uparams = self.get_uparams(ws)?;
        let definition = DefinitionVal::new(self.env_handle.clone(), 
                                            name,
                                            uparams,
                                            ty,
                                            val);

        add_definition(definition, self.env_handle.clone(), true)
    }

    pub fn make_quotient(&mut self) -> NanodaResult<()> {
        let new_quot = Quot::new();
        for elem in new_quot.inner.into_iter() {
            add_quot(elem, self.env_handle.clone())?;
        }
        // set environment's `quot_is_init` flag to `true`; enables
        // typechecker to use the quotient reduction procedure.
        Ok(self.env_handle.write().init_quot())
    }

    pub fn make_inductive(&mut self, ws : &mut SplitWhitespace) -> NanodaResult<()> {
        let num_params = self.parse_usize(ws)?;
        let name = self.get_name(ws)?;

        let ty = self.get_expr(ws)?;
        let num_intros = self.parse_usize(ws)?;
        let rest_usize = self.parse_rest_usize(ws)?;
        let (intros, params) = rest_usize.split_at(2 * num_intros);

        let param_vec = params.into_iter().map(|idx| {
            let fetched_name = self.names.get(*idx).cloned().unwrap_or_else(|| self.ref_anon());
            mk_param(fetched_name)
        }).collect::<Vec<Level>>();

        let mut intros_buf : Vec<(Name, Expr)> = Vec::new();

        for two_slice in intros.chunks(2usize) {
            let name = self.names.get(two_slice[0]).cloned().unwrap_or_else(|| self.ref_anon());
            let ty = self.exprs.get(two_slice[1]).cloned().unwrap_or_else(|| self.ref_prop());
            intros_buf.push((name, ty));
        }


        let constr_buf = intros_buf.clone().into_iter().map(|(n, e)| {
            Constructor::new(&n, &e)
        }).collect::<Vec<Constructor>>();

        let ind_type = InductiveType::new(name.clone(), ty.clone(), constr_buf);
        let ind = InductiveDeclar::new(
            name,
            param_vec,
            num_params, 
            vec![ind_type], 
            false);

        add_inductive(ind, self.env_handle.clone(), true)
    }


}


// FIXME add command-line flag for strict/non-strict export file parsing.
// Strict assumes that well-formed export files will not have 'holes' when filling
// in comopnent arrays; IE all items will be placed consecutively.
fn write_elem_strict<T>(v : &mut Vec<T>, new_elem : T, pos : usize) -> NanodaResult<()> {
    assert!(v.len() == pos);
    match v.get_mut(pos) {
        Some(_) => { 
            eprintln!("malformed export file; components should never require replacement within vectors.");
            std::process::exit(-1);
        },
        None => {
            v.push(new_elem);
        }
    }
    Ok(())
}




