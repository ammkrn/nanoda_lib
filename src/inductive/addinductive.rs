use crate::inductive::newinductive::{ get_all_inductive_names, InductiveType };
use crate::recursor::RecInfo;

use crate::utils::{ HasInstantiate, ShortCircuit::* };
use crate::name::Name;
use crate::level::{ Level, mk_param, mk_zero };
use crate::recursor::{ RecursorVal, RecursorRule };
use crate::env::{ ArcEnv, 
                  ConstantInfo,
                  InductiveVal,
                  ConstructorVal,
                  ensure_no_dupe_lparams };
use crate::tc::{ TypeChecker };
use crate::expr::{ Expr, 
                   mk_local_declar,
                   mk_local_declar_for,
                   BinderStyle, 
                   InnerExpr::*, 
                   mk_const, 
                   mk_var,
                   mk_sort, 
                   mk_app };
use crate::errors::{ NanodaResult, NanodaErr::* };



// inductive.cpp ~78
#[derive(Debug)]
pub struct AddInductiveFn {
    //m_lctx : LocalCtx,
    name : Name,
    m_lparams : Vec<Level>,
    m_levels : Vec<Level>, 
    m_nparams : usize,
    m_is_unsafe : bool,
    m_ind_types : Vec<InductiveType>,
    env_handle : ArcEnv,
    m_nindices : Vec<usize>,
    m_result_level : Level,
    m_is_not_zero : Option<bool>, 
    m_params : Vec<Expr>, 
    m_ind_consts : Vec<Expr>, 
    m_elim_level : Level,
    m_K_target : bool,
    m_rec_infos : Vec<RecInfo>,
    use_dep_elim : Option<bool>,
}

impl AddInductiveFn {
    pub fn new(name : Name,
               m_lparams : Vec<Level>,
               m_nparams : usize,
               m_is_unsafe : bool,
               m_ind_types : Vec<InductiveType>,
               env_handle : ArcEnv) -> Self {
        AddInductiveFn {
            name,
            m_lparams,
            m_levels : Vec::new(),
            m_nparams,
            m_is_unsafe,
            m_ind_types,
            m_nindices : Vec::new(),
            m_result_level : mk_zero(),
            m_is_not_zero : None,
            m_params : Vec::new(),
            m_ind_consts : Vec::new(),
            m_elim_level : mk_zero(),
            m_K_target : false,
            m_rec_infos : Vec::new(),
            use_dep_elim : None,
            env_handle,
        }
    }

    pub fn add_inductive_core(&mut self) -> NanodaResult<()> {
        ensure_no_dupe_lparams(&self.m_lparams)?;
        self.check_inductive_types()?;
        self.declare_inductive_types()?;
        self.check_constructors()?;
        self.declare_constructors();
        self.init_elim_level()?;
        self.init_k_target()?;
        self.mk_rec_infos()?;
        self.declare_recursors()
    }

    pub fn get_param_type(&self, idx : usize) -> NanodaResult<&Expr> {
        match self.m_params.get(idx).map(|e| e.as_ref()) {
            Some(Local { binder, .. }) => Ok(&binder.type_),
            _ => Err(GetParamTypeErr)
        }
    }

    pub fn use_dep_elim(&self, base_type : &Expr) -> NanodaResult<bool> {
        match base_type.as_ref() {
            Sort { level, .. } => Ok(level.maybe_nonzero()),
            _ => Err(UseDepElimNotSortErr)
        }
    }

    pub fn check_inductive_types(&mut self) -> NanodaResult<()> {
        self.m_levels = self.m_lparams.clone();

        let mut tc = TypeChecker::new(None, self.env_handle.clone());

        // We might potentially have multiple types in the case of
        // mutual declarations.
        for (idx, elem) in self.m_ind_types.iter().enumerate() {
            let mut base_type = elem.type_.clone();
            assert!(!base_type.has_locals());

            // collect level param names for type check.
            // check that the base type is correctly formed.
            //tc.check(&base_type, self.m_lparams.clone());
            base_type.checked_infer(self.m_lparams.clone(), &mut tc);

            let mut nindices_counter = 0usize;
            let mut i = 0usize;

            while let Pi { binder, body, .. } = base_type.as_ref() {
                if i < self.m_nparams {
                    if (idx == 0) {
                        let param_ = mk_local_declar_for(&base_type);
                        base_type = body.instantiate(Some(&param_).into_iter());
                        self.m_params.push(param_);
                    } else {
                        let indexed_param = self.m_params.get(i).ok_or_else(|| BadIndexErr(file!(), line!(), i))?;
                        //assert!(tc.is_def_eq(&binder.type_, indexed_param.get_local_type()?) == EqShort) ;
                        assert!(binder.type_.check_def_eq(indexed_param.get_local_type()?, &mut tc) == EqShort);
                        base_type = body.instantiate(Some(indexed_param).into_iter());
                    }
                    i += 1;
                } else {
                    base_type = body.clone();
                    nindices_counter += 1;
                }
            }

            self.m_nindices.push(nindices_counter);

            if i != self.m_nparams {
                crate::errors::check_inductive_i_neq(line!(), i, self.m_nparams);
            }

            let infd_sort = base_type.ensure_sort(&mut tc);
            base_type = infd_sort.clone();

            self.use_dep_elim = Some(self.use_dep_elim(&base_type)?);

            if (idx == 0) {
                let result_level = base_type.get_sort_level()?;
                let is_not_zero = result_level.is_nonzero();
                self.m_result_level = result_level.clone();
                self.m_is_not_zero = Some(is_not_zero);
            } else if !(infd_sort.get_sort_level()?.eq_by_antisymm(&self.m_result_level)) {
                crate::errors::mutual_different_universes(line!(), infd_sort.get_sort_level()?, &self.m_result_level);
            }

            let ind_const = mk_const(elem.name.clone(), self.m_levels.clone());
            self.m_ind_consts.push(ind_const);
        }
        assert_eq!(self.m_lparams.len(), self.m_levels.len());
        assert_eq!(self.m_nindices.len(), self.m_ind_types.len());
        assert_eq!(self.m_ind_consts.len(), self.m_ind_types.len());
        assert_eq!(self.m_params.len(), self.m_nparams);
        Ok(())
    }

    pub fn declare_inductive_types(&self) -> NanodaResult<()> {
        for idx in 0..self.m_ind_types.len() {
            let ind_type = self.m_ind_types.get(idx)
                           .ok_or_else(|| BadIndexErr(file!(), line!(), idx))?;

            let inductive_val = InductiveVal::new(
                ind_type.name.clone(),
                self.m_lparams.clone(),
                ind_type.type_.clone(),
                self.m_nparams,
                *self.m_nindices.get(idx).ok_or_else(|| BadIndexErr(file!(), line!(), idx))?,
                get_all_inductive_names(&self.m_ind_types),
                ind_type.constructors.iter().map(|cnstr| cnstr.name.clone()).collect(),
                self.is_rec(),
                self.m_is_unsafe,
                self.is_reflexive()
            );

            let as_const_info = ConstantInfo::InductiveInfo(inductive_val);
            assert_eq!(&ind_type.name, &as_const_info.get_constant_base().name);

            self.env_handle
            .write()
            .add_constant_info(as_const_info)
        }
        Ok(())
    }

    fn is_rec(&self) -> bool {
        let predicate = |e : &Expr| 
        if let Const { name, .. } = e.as_ref() {
            self.m_ind_consts.iter().filter_map(|c| c.get_const_name()).any(|n| n == name)
        } else {
            false
        };

        self.m_ind_types.iter()
            .flat_map(|ind_type| ind_type.constructors.iter())
            .any(|cnstr| {
                let mut cursor = &cnstr.type_;
                while let Pi { binder, body, .. } = cursor.as_ref() {
                    if binder.type_.find_matching(predicate).is_some() {
                        return true
                    }
                    cursor = body;
                }
                false
            })
    }

    // only used as a check in is_reflexive
    // does self.ind_consts contain any other items with the same
    // const name as e?
    fn is_ind_occurrence(&self, _e : &Expr) -> bool {
        if let Const { name, .. } = _e.as_ref() {
            self.m_ind_consts.iter().all(|cnst| {
                cnst.get_const_name().map(|n| n == name).unwrap_or(false)
            })
        } else {
            false
        }
    }


    // return true if the given declaration is reflexive.
    /*
    An inductive type `T` is reflexive if it contains at least one
    constructor that takes as an argument a function returning `T`,
    where `T` is another inductive datatype (possibly `T`) in the same
    mutual declaration
    */ 
    fn is_reflexive(&self) -> bool {
        self.m_ind_types.iter()
        .flat_map(|ind_type| ind_type.constructors.iter())
        .any(|cnstr| {
            let mut cursor = cnstr.type_.clone();

            while let Pi { binder, body, .. } = cursor.as_ref() {
                if binder.type_.as_ref().is_pi() && self.is_ind_occurrence(&binder.type_) {
                    return true
                } else {
                    let local = mk_local_declar_for(&cursor);
                    cursor = body.instantiate(Some(&local).into_iter());
                }
            }

            false

        })
    }

    pub fn is_valid_ind_app2(&self, t : &Expr, idx : usize) -> bool {
        let (I, args) = t.unfold_apps_rev();
        let cond1 = ((I) != ((&self.m_ind_consts[idx])));
        let cond2 = args.len() != (self.m_nparams + (&self.m_nindices[idx]));
        if (cond1 || cond2) {
            return false
        } else {
            for i in 0..self.m_nparams {
                let cond_check = (self.m_params[i].eq_mod_serial(&args[i]));
                if !cond_check {
                    let _x = &self.m_params[i];
                    let _y = &args[i];

                    return false
                }
            }
        }
        return true
    }

    pub fn is_valid_ind_app(&self, _e : &Expr) -> Option<usize> {
        for idx in 0..self.m_ind_types.len() {
            if self.is_valid_ind_app2(_e, idx) {
                return Some(idx)
            }
        }
        None
    }

    pub fn is_rec_argument(&self, _e : &Expr, tc : &mut TypeChecker) -> Option<usize> {
        let mut cursor = _e.whnf(tc);
        while let Pi { body, .. } = cursor.as_ref() {
            let local = mk_local_declar_for(&cursor);

            let instd = body.instantiate(Some(&local).into_iter());
            cursor = instd.whnf(tc);
        }

        self.is_valid_ind_app(&cursor)
    }

    pub fn check_positivity(&self, _t : &Expr, cnstr_name : &Name, arg_idx : usize, tc : &mut TypeChecker) -> NanodaResult<()> {
        let whnfd = _t.whnf(tc);
        if !self.is_ind_occurrence(&whnfd) {
            Ok(())
        } else if let Pi { binder, body, .. } = whnfd.as_ref() {
            if self.is_ind_occurrence(&binder.type_) {
                Err(NonposOccurrenceErr(file!(), line!()))
            } else {
                let local = mk_local_declar_for(&whnfd);
                //let instd = body.instantiate(Some(&local).into_iter());
                let instd = body.instantiate(Some(&local).into_iter());
                self.check_positivity(&instd, cnstr_name, arg_idx, tc)
            }
        } else if self.is_valid_ind_app(&whnfd).is_some() {
            Ok(())
        } else {
            Err(InvalidOccurrenceErr(file!(), line!()))
        }
    }


    pub fn check_constructors(&self) -> NanodaResult<()> {
        let mut tc = TypeChecker::new(None, self.env_handle.clone());
        for idx in 0..self.m_ind_types.len() {
            let ind_type = &self.m_ind_types[idx];
            for cnstr in ind_type.constructors.iter() {
                let n = &cnstr.name;
                let mut t = cnstr.type_.clone();
                // FIXME
                // m_env.check_name(n);
                assert!(t.var_bound() == 0);
                t.checked_infer(self.m_lparams.clone(), &mut tc);
                let mut i = 0usize;
                while let Pi { binder : dom, body, .. } = t.as_ref() {
                    if i < self.m_nparams {
                        if dom.type_.check_def_eq(self.get_param_type(i)?, &mut tc) == NeqShort {
                            return Err(CnstrBadParamTypeErr)
                        } else {
                            let l = &self.m_params[i];
                            let instd = body.instantiate(Some(l).into_iter());
                            t = instd;
                        }
                    } else {
                        let s = dom.type_.ensure_type(&mut tc);
                        let cond1 = self.m_result_level.is_geq(s.get_sort_level()?);
                        let cond2 = self.m_result_level.is_zero();

                        if !(cond1 || cond2) {
                            return Err(CnstrUnivErr)
                        }

                        if !self.m_is_unsafe {
                            self.check_positivity(&dom.type_, n, i, &mut tc)?;
                        }

                        let local = mk_local_declar_for(&t);
                        let instd = body.instantiate(Some(&local).into_iter());
                        t = instd;
                    }
                    i += 1;
                }

                if !self.is_valid_ind_app2(&t, idx) {
                    return Err(CnstrBadTypeErr)
                }
            }
        }
        Ok(())
    }


    pub fn declare_constructors(&self) {
        for idx in 0..self.m_ind_types.len() {
            let ind_type = &self.m_ind_types[idx];
            let mut cidx = 0usize;
            for cnstr in ind_type.constructors.iter() {
                let n = cnstr.name.clone();
                let t = cnstr.type_.clone();
                let mut arity = 0usize;
                let mut it = t.clone();
                while let Pi { body, .. } = it.as_ref() {
                    it = body.clone();
                    arity += 1;
                }

                assert!(arity >= self.m_nparams);
                let nfields = arity - self.m_nparams;

                let cval = ConstructorVal::new(
                    n.clone(),
                    self.m_lparams.clone(),
                    t.clone(),
                    ind_type.name.clone(),
                    cidx,
                    self.m_nparams,
                    nfields,
                    self.m_is_unsafe
                );

                let as_const_info = ConstantInfo::ConstructorInfo(cval);
                assert_eq!(&n, &as_const_info.get_constant_base().name);
                self.env_handle
                .write()
                .add_constant_info(as_const_info);
                cidx += 1;
            }
        }
    }

    pub fn elim_only_at_universe_zero(&self, tc : &mut TypeChecker) -> NanodaResult<bool> {
        if self.m_is_not_zero
           .ok_or_else(|| NoneErr(file!(), line!(), "elim_only_at_universe_zero::m_is_not_zero"))? {
            return Ok(false)
        }

        if self.m_ind_types.len() > 1 {
            return Ok(true)
        }

        let num_intros = (&self.m_ind_types[0]).constructors.len();

        if num_intros > 1 {
            return Ok(true)
        }

        if num_intros == 0 {
            return Ok(false)
        }

        let mut cnstr_type = (&self.m_ind_types[0].constructors.get(0))
                    .ok_or_else(|| NoneErr(file!(), line!(), "inductive::elim_only_at_univserse_zero::cnstr"))?
                    .type_
                    .clone();

        let mut i = 0usize;
        let mut to_check = Vec::new();

        while let Pi { binder : dom, body, .. } = cnstr_type.as_ref() {
            let fvar = mk_local_declar_for(&cnstr_type);
            if i >= self.m_nparams {
                //let s = tc.ensure_type(&dom.type_);
                let s = dom.type_.ensure_type(tc);
                if (!(s.get_sort_level()?.is_zero())) {
                    to_check.push(fvar.clone());
                }
            }

            let instd = body.instantiate(Some(&fvar).into_iter());
            cnstr_type = instd;
            i += 1;
        }

        let (_, result_args) = cnstr_type.unfold_apps_rev();

        for arg in to_check.iter() {
            if !(result_args.contains(&arg)) {
                return Ok(true)
            }
        }

        Ok(false)
    }

    pub fn init_elim_level(&mut self) -> NanodaResult<()> {
        let mut tc = TypeChecker::new(None, self.env_handle.clone());
        let result = if self.elim_only_at_universe_zero(&mut tc)? {
            self.m_elim_level = mk_zero();
        } else {
            let mut n = Name::from("u");
            let mut counter = 1u64;
            while self.m_lparams.iter().any(|x| x.get_param_name() == &n) {
                n = n.extend_num(counter);
                counter += 1;
            }

            self.m_elim_level = mk_param(n);

        };
        Ok(result)

    }

    // This one doesn't admit punit as a target for k-like reduction since 
    // its result_level is Sort(u). The other ones are eq, heq, and true, which
    // are all m_result_level == Sort(0) AKA Props.
    pub fn init_k_target(&mut self) -> NanodaResult<()> {
        let cond1 = self.m_ind_types.len() == 1;
        let cond2 = self.m_result_level.is_zero();
        let cond3 = (&self.m_ind_types[0]).constructors.len() == 1;
        self.m_K_target = cond1 && cond2 && cond3;

        if (!self.m_K_target) {
            return Ok(())
        } 

        let mut it = (&self.m_ind_types[0])
        .constructors
        .get(0)
        .ok_or_else(|| NoneErr(file!(), line!(), "inductive::init_k_target(0)"))?
        .type_
        .clone();

        let mut i = 0usize;
        while let Pi { body, .. } = it.as_ref() {
            if (i < self.m_nparams) {
                it = body.clone();
            } else {
                self.m_K_target = false;
                break;
            }
            i += 1;
        }
        Ok(())
    }

    pub fn get_I_indices(&self, t : Expr, indices : &mut Vec<Expr>) -> NanodaResult<usize> {
        let r : usize = self.is_valid_ind_app(&t)
                        .ok_or_else(|| NoneErr(file!(), line!(), "inductive::get_I_indices"))?;

        let (_, all_args) = t.unfold_apps_rev();
        for i in self.m_nparams .. all_args.len() {
            indices.push((&all_args[i]).clone().clone());
        }

        Ok(r)
    }

    // This function is horrifying.
    pub fn mk_rec_infos(&mut self) -> NanodaResult<()> {
        let mut tc = TypeChecker::new(None, self.env_handle.clone());
        let mut d_idx = 0usize;

        for ind_type in self.m_ind_types.iter() {
            // FIXME
            let mut rec_info = RecInfo::new(mk_var(0), Vec::new(), Vec::new(), mk_var(0));

            let mut t : Expr = ind_type.type_.clone();
            let mut i = 0usize;

            while let Pi { body, .. } = t.as_ref() {
                if (i < self.m_nparams) {
                    let l = &self.m_params[i];
                    let instd = body.instantiate(Some(l).into_iter());
                    t = instd;
                } else {
                    let idx = mk_local_declar_for(&t);
                    rec_info.m_indices.push(idx.clone());
                    // set m_indices
                    let instd = body.instantiate(Some(&idx).into_iter());
                    t = instd;
                }

                i += 1;
            }


            let _app = (&self.m_ind_consts[d_idx])
                       .foldl_apps(self.m_params.iter())
                       .foldl_apps(rec_info.m_indices.iter());
            let major_local = mk_local_declar(Name::from("t"), _app, BinderStyle::Default);
            rec_info.m_major = major_local;

            let MotiveBase = mk_sort(self.m_elim_level.clone());
            let use_dep_elim_res = self.use_dep_elim.ok_or_else(|| NoneErr(file!(), line!(), "mk_rec_infos::use_dep_elim"))?;
            let MotiveType = if use_dep_elim_res {
                let _x = MotiveBase.fold_pis(Some(&rec_info.m_major).into_iter());
                _x.fold_pis(rec_info.m_indices.iter())
            } else {
                MotiveBase.fold_pis(rec_info.m_indices.iter())
            };

            let mut MotiveName = Name::from("C");
            if self.m_ind_types.len() > 1 {
                MotiveName = MotiveName.extend_num((d_idx + 1) as u64);
            }

            let Motive = mk_local_declar(MotiveName.clone(), MotiveType.clone(), BinderStyle::Implicit);
            rec_info.m_C = Motive.clone();
            self.m_rec_infos.push(rec_info);
            d_idx += 1;
        }

        let mut minor_idx = 1usize;
        d_idx = 0;

        for ind_type in self.m_ind_types.iter() {
            for cnstr in ind_type.constructors.iter() {
                let mut b_u = Vec::<Expr>::new();
                let mut u = Vec::<Expr>::new();
                let mut v = Vec::<Expr>::new();
                let mut t : Expr = cnstr.type_.clone();

                let mut i = 0usize;

                while let Pi { binder : dom, body, .. } = t.as_ref() {
                    if (i < self.m_nparams) {
                        let instd = body.instantiate(Some(&self.m_params[i]).into_iter());
                        t = instd;
                    } else {
                        let l = mk_local_declar_for(&t);
                        b_u.push(l.clone());
                        if self.is_rec_argument(&dom.type_, &mut tc).is_some() {
                            u.push(l.clone());
                        }
                        let instd = body.instantiate(Some(&l).into_iter());
                        t = instd;

                    }
                    i += 1;
                }

                let mut it_indices = Vec::<Expr>::new();

                let it_idx = self.get_I_indices(t.clone(), &mut it_indices)?;

                let use_dep_elim_result = self.use_dep_elim
                                         .ok_or_else(|| NoneErr(file!(), line!(), "inductive::declare_recursors, use_dep_elim_result"))?;

                let MotiveAppBase = (&self.m_rec_infos[it_idx].m_C).foldl_apps(it_indices.iter());
                let MotiveApp = if use_dep_elim_result {
                    let rhs = mk_const(cnstr.name.clone(), self.m_levels.clone())
                              .foldl_apps(self.m_params.iter())
                              .foldl_apps(b_u.iter());

                    mk_app(MotiveAppBase, rhs)
                } else {
                    MotiveAppBase
                };


                for i in 0..u.len() {
                    let u_i = &u[i];
                    let infd = u_i.infer_type(&mut tc);
                    let mut u_i_ty = infd.whnf(&mut tc);

                    let mut xs = Vec::new();

                    while let Pi { body, .. } = u_i_ty.as_ref() {
                        let x = mk_local_declar_for(&u_i_ty);
                        xs.push(x.clone());
                        let instd = body.instantiate(Some(&x).into_iter());
                        let whnfd = instd.whnf(&mut tc);
                        u_i_ty = whnfd;
                    }

                    let mut it_indices = Vec::<Expr>::new();
                    let it_idx = self.get_I_indices(u_i_ty.clone(), &mut it_indices)?;
                    let C_Base = (&self.m_rec_infos[it_idx].m_C).foldl_apps(it_indices.iter());

                    let C_Base2 = if use_dep_elim_result {
                        let u_app = u_i.foldl_apps(xs.iter());
                        mk_app(C_Base, u_app)
                    } else {
                        C_Base
                    };

                    let v_i_ty = C_Base2.fold_pis(xs.iter());
                    let v_i = mk_local_declar(Name::from("v").extend_num(i as u64), v_i_ty.clone(), BinderStyle::Default);
                    v.push(v_i);
                }

                let minor_ty_pre = MotiveApp.fold_pis(v.iter());
                let minor_ty = minor_ty_pre.fold_pis(b_u.iter());
                let minor = mk_local_declar(Name::from("m").extend_num(minor_idx as u64), minor_ty, BinderStyle::Default);
                (&mut self.m_rec_infos[d_idx]).m_minors.push(minor);
                minor_idx += 1;
            }

            d_idx += 1;

        }
        Ok(())
    }

    pub fn get_rec_levels(&self) -> Vec<Level> {
        if self.m_elim_level.is_param() {
            let mut v = Vec::new();
            v.push(self.m_elim_level.clone());
            for l in self.m_levels.clone() {
                v.push(l)
            }
            v
        } else {
            Vec::from(self.m_levels.clone())
        }
    }

    // These are implemented as `fill a given mutable ref to a vec` functions.
    pub fn collect_Cs(&self) -> Vec<Expr> {
        let mut v = Vec::new();
        for i in 0 .. self.m_ind_types.len() {
            v.push((&self.m_rec_infos[i]).m_C.clone());
        }
        v
    }

    pub fn collect_minor_premises(&self) -> Vec<Expr> {
        let mut v = Vec::new();
        for i in 0 .. self.m_ind_types.len() {
            v.extend((&self.m_rec_infos[i]).m_minors.clone());
        }
        v
    }


    pub fn mk_rec_rules(&self, tc : &mut TypeChecker, d_idx : usize, Cs : &mut Vec<Expr>, minors : &mut Vec<Expr>, mut minor_idx : usize) -> NanodaResult<Vec<RecursorRule>> {
        let d = &self.m_ind_types[d_idx].clone();
        let lvls = self.get_rec_levels();
        let mut rules = Vec::<RecursorRule>::new();

        for cnstr in d.constructors.iter() {
            let mut b_u = Vec::<Expr>::new();
            let mut u = Vec::<Expr>::new();
            let mut t = cnstr.type_.clone();

            let mut i = 0usize;

            while let Pi { binder : dom, body, .. } = t.as_ref() {
                if (i < self.m_nparams) {
                    let instd = body.instantiate(Some(&self.m_params[i]).into_iter());
                    t = instd;
                } else {
                    let l = mk_local_declar_for(&t);
                    b_u.push(l.clone());
                    if (self.is_rec_argument(&dom.type_, tc).is_some()) {
                        u.push(l.clone());
                    }
                    let instd = body.instantiate(Some(&l).into_iter());
                    t = instd
                }

                i += 1;

            }

            let mut v = Vec::<Expr>::new();

            for i in 0..u.len() {
                let u_i = &u[i].clone();
                let infd = u_i.infer_type(tc);
                let mut u_i_ty = infd.whnf(tc);

                let mut xs = Vec::<Expr>::new();

                while let Pi { body, .. } = u_i_ty.as_ref() {
                    let x = mk_local_declar_for(&u_i_ty);
                    xs.push(x.clone());
                    let instd = body.instantiate(Some(&x).into_iter());
                    u_i_ty = instd.whnf(tc);
                }

                let mut it_indices = Vec::<Expr>::new();
                let it_idx = self.get_I_indices(u_i_ty.clone(), &mut it_indices)?;
                let rec_name = (&self.m_ind_types[it_idx]).name.mk_rec_name();

                let rec_app_lhs = mk_const(rec_name, Vec::from(lvls.clone()))
                                  .foldl_apps(self.m_params.iter())
                                  .foldl_apps(Cs.iter())
                                  .foldl_apps(minors.iter())
                                  .foldl_apps(it_indices.iter());
                let rec_app = mk_app(rec_app_lhs, u_i.foldl_apps(xs.iter()));
                v.push(rec_app.fold_lambdas(xs.iter()));
            }



            let comp_rhs = (&minors[minor_idx]).foldl_apps(b_u.iter())
                            .foldl_apps(v.iter())
                            .fold_lambdas(b_u.iter())
                            .fold_lambdas(minors.iter())
                            .fold_lambdas(Cs.iter())
                            .fold_lambdas(self.m_params.iter());

            let rec_rule = RecursorRule::new(cnstr.name.clone(), b_u.len(), comp_rhs);

            rules.push(rec_rule);
            minor_idx += 1;
        }


        Ok(rules)

    }

    pub fn get_all_inductive_names(&self) -> Vec<Name> {
        let mut v = Vec::new();
        for elem in self.m_ind_types.iter() {
            v.push(elem.name.clone());
        }
        v
    }

    pub fn declare_recursors(&mut self) -> NanodaResult<()> {
        let mut Cs = self.collect_Cs();
        let mut minors = self.collect_minor_premises();

        let nminors = minors.len();
        let nmotives = Cs.len();

        let all : Vec<Name> = self.get_all_inductive_names();

        let minor_idx = 0usize;

        let mut tc = TypeChecker::new(None, self.env_handle.clone());

        for d_idx in 0..(self.m_ind_types.len()) {
            let use_dep_elim_result = self.use_dep_elim
                                     .ok_or_else(|| NoneErr(file!(), line!(), "inductive::declare_recursors, use_dep_elim_result"))?;

            let info = &self.m_rec_infos[d_idx].clone();

            let MotiveAppBase = info.m_C.foldl_apps(info.m_indices.iter());

            let MotiveApp = if use_dep_elim_result {
                mk_app(MotiveAppBase, info.m_major.clone())
            } else {
                MotiveAppBase
            };

            let rec_ty = MotiveApp.fold_pis(Some(&info.m_major).into_iter())
                         .fold_pis(info.m_indices.iter())
                         .fold_pis(minors.iter())
                         .fold_pis(Cs.iter())
                         .fold_pis(self.m_params.iter());

            //// This is unused (by the kernel) apparently.
            //let rec_ty = rec_ty.infer_implicit(true);
            let rules = self.mk_rec_rules(&mut tc, d_idx, &mut Cs, &mut minors, minor_idx)?;
            let rec_name = (&self.m_ind_types[d_idx].name).mk_rec_name();

            let recursor_val = RecursorVal::new(
                rec_name.clone(),
                self.get_rec_levels(),
                rec_ty.clone(),
                all.clone(),
                self.m_nparams.clone(),
                self.m_nindices[d_idx],
                nmotives,
                nminors,
                rules,
                self.m_K_target,
                self.m_is_unsafe,
            );


            let as_const_info = ConstantInfo::RecursorInfo(recursor_val);
            assert_eq!(&rec_name, &as_const_info.get_constant_base().name);

            tc.env
            .write()
            .add_constant_info(as_const_info);
        }
        Ok(())
    }
}