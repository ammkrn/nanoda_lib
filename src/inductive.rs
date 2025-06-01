use crate::env::{ConstructorData, Declar, DeclarInfo, DeclarMap, InductiveData, RecRule, RecursorData};
use crate::expr::{BinderStyle, Expr::*};
use crate::tc::{InferFlag, TypeChecker};
use crate::util::{ExportFile, ExprPtr, FxIndexMap, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use std::sync::Arc;

impl<'t, 'p: 't> ExportFile<'p> {
    pub(crate) fn check_inductive_declar(&self, ind: &InductiveData<'t>) {
        self.with_ctx(|ctx| {
            // The **unmodified** types and constructors for all of the types in this mutual block.
            let unmodified_tys_ctors = ctx.with_tc(|tc| {
                tc.check_declar_info(&ind.info);
                tc.collect_unmodified_mutuals(ind)
            });

            // Initialize the big chunk of state used throughout the process of checking
            // this inductive declaration.
            let mut st = ctx.with_tc(|tc| tc.specialize_nested(ind, unmodified_tys_ctors.clone()));

            // Check the (potentially modified) inductive specs against the base environment.
            ctx.with_tc(|tc| tc.check_inductive_specs(&mut st));

            // The first temporary environment extension, containing any specialized
            // types to deal with nested inductives.
            let ind_ty_ext1 = ctx.mk_ind_tys_env_ext(&st);

            // Check the constructors against the environment with the base extension.
            ctx.with_tc_and_env_ext(&ind_ty_ext1, |tc| {
                for ind in st.all_inductives_incl_specialized.iter() {
                    for ctor in ind.ctors.iter() {
                        tc.check_ctor(&st, ind.name, ctor.ty)
                    }
                }
            });

            // The second temporary environment extension, which also includes the constructors.
            let ctor_extension = ctx.mk_ctors_env_ext(&st, ind_ty_ext1);

            // The constructed recursors and rec rules
            let recursors = ctx.with_tc_and_env_ext(&ctor_extension, |tc| {
                tc.mk_elim_level(&mut st);
                tc.init_k_target(&mut st);
                tc.mk_majors(&mut st);
                tc.mk_motives(&mut st);
                tc.mk_minors(&mut st);
                tc.mk_recursors(&st)
            });

            // The last temporary environment extension, which also includes the recursors.
            let recursor_extension = {
                let mut out = ctor_extension;
                for r in recursors.clone() {
                    out.insert(r.info().name, r);
                }
                out
            };

            ctx.with_tc_and_env_ext(&recursor_extension, |tc| {
                if st.is_nested() {
                    tc.restore_and_check(&st, &unmodified_tys_ctors, &ind.all_ind_names);
                } else {
                    // Do the definitional equality assertions of new/old here.
                    tc.assert_nonnested_tys_def_eq(ind, &st);
                    tc.assert_nonnested_ctors_def_eq(&st);
                    tc.assert_nonnested_recursors_def_eq(&st, &recursors);
                }
            })
        })
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Extend the current environment with the inductive specifications,
    /// including modifications to accommodate any temporary declarations
    /// that come from nested inductives.
    ///
    /// Then assert that any of the inductive types in the temporary extension
    /// which are also in the export file are def_eq to those in the export file.
    fn mk_ind_tys_env_ext(&mut self, st: &InductiveCheckState<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        let is_nested = !st.nested_to_unspecialized_ty_nofvars.is_empty();
        let all_ind_names: Arc<[NamePtr]> = st.all_inductives_incl_specialized.iter().map(|x| x.name).collect();
        let mut env_extension = crate::util::new_fx_index_map();
        for (idx, inductive) in st.all_inductives_incl_specialized.iter().enumerate() {
            let t = Declar::Inductive(InductiveData {
                info: DeclarInfo { name: inductive.name, ty: inductive.ty, uparams: st.uparams },
                is_nested,
                is_recursive: false,
                num_params: u16::try_from(st.local_params.len()).unwrap(),
                num_indices: u16::try_from((st.local_indices[idx]).len()).unwrap(),
                all_ind_names: all_ind_names.clone(),
                all_ctor_names: inductive.ctors.iter().map(|x| x.name).collect(),
            });
            env_extension.insert(inductive.name, t);
        }
        env_extension
    }

    /// Extend the current environment with new constructors, including modifications
    /// to accommodate any temporary declarations that come from nested inductives.
    fn mk_ctors_env_ext(&mut self, nest_st: &InductiveCheckState<'t>, mut env_ext: DeclarMap<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        for inductive in nest_st.all_inductives_incl_specialized.iter() {
            for (idx, ctor) in inductive.ctors.iter().copied().enumerate() {
                let info = DeclarInfo { name: ctor.name, ty: ctor.ty, uparams: nest_st.uparams };
                let num_params = u16::try_from(nest_st.local_params.len()).unwrap();
                let num_fields = self.pi_telescope_size(ctor.ty) - num_params;
                let d = Declar::Constructor(ConstructorData {
                    info,
                    inductive_name: inductive.name,
                    ctor_idx: u16::try_from(idx).unwrap(),
                    num_params,
                    num_fields,
                });
                env_ext.insert(ctor.name, d);
            }
        }
        env_ext
    }
}

pub(crate) struct InductiveCheckState<'a> {
    /// Maps the specialized type's fresh name to its "actual"/unspecialized type,
    /// where the unspecialized type retains free variables.
    ///   
    /// Example contents for `Sexpr`:\
    /// ```ignore
    /// (_nested.List_1, (List.[u] (Sexpr.[u] #(α, Unique(0) : Sort(u + 1)))))
    /// ```
    ///
    /// Example contents for `Lean.Syntax`:\
    /// ```ignore
    /// (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
    /// (_nested.List_2, (List.[0] Lean.Syntax.[]))
    /// ```
    nested_to_unspecialized_ty_wfvars: FxIndexMap<NamePtr<'a>, ExprPtr<'a>>,
    /// Maps the specialized type's fresh name to its "actual"/unspecialized type,
    /// where the type uses bound variables instead of free variables.
    ///
    /// Example contents for `Sexpr`:\
    /// ```ignore
    /// (_nested.List_1, (List.[u] (Sexpr.[u] $0)))
    /// ```
    ///
    /// Example contents for `Lean.Syntax`:\
    /// ```ignore
    /// (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
    /// (_nested.List_2, (List.[0] Lean.Syntax.[]))
    /// ```
    nested_to_unspecialized_ty_nofvars: FxIndexMap<NamePtr<'a>, ExprPtr<'a>>,
    uparams: LevelsPtr<'a>,
    // NOTE: All of the inductives in a mutual block have to be declared with the same
    // number of parameters, and after specialization, the mutuals that are specialized
    // nested types will also have the same number of params as the block. This means that
    // if a nested container type has fewer params than the block, the block will gain more
    // parameters.
    num_params: u16,
    /// This is all of the inductive types in the current mutual block, PLUS any temoprary extensions
    /// generated by nested inductives.
    all_inductives_incl_specialized: Vec<IndTyHeader<'a>>,
    /// Used for generating fresh names when specializing nested inductives.
    /// Needs to be incrementing because you may have more than one specialized
    /// version of a given container type.
    next_ngen_idx: u64,
    local_params: Vec<ExprPtr<'a>>,
    local_indices: Vec<Vec<ExprPtr<'a>>>,
    block_codom: Option<LevelPtr<'a>>,
    is_zero: Option<bool>,
    is_nonzero: Option<bool>,
    ind_consts: Vec<ExprPtr<'a>>,
    rec_uparams: Option<LevelsPtr<'a>>,
    elim_level: Option<LevelPtr<'a>>,
    k_target: Option<bool>,
    majors: Vec<ExprPtr<'a>>,
    motives: Vec<ExprPtr<'a>>,
    minors: Vec<Vec<ExprPtr<'a>>>,
}

impl<'a> InductiveCheckState<'a> {
    fn new(
        info_uparams: LevelsPtr<'a>,
        num_params: u16,
        new_tys: Vec<IndTyHeader<'a>>,
        local_params: Vec<ExprPtr<'a>>,
    ) -> Self {
        Self {
            nested_to_unspecialized_ty_wfvars: crate::util::new_fx_index_map(),
            nested_to_unspecialized_ty_nofvars: crate::util::new_fx_index_map(),
            uparams: info_uparams,
            num_params,
            all_inductives_incl_specialized: new_tys,
            next_ngen_idx: 1u64,
            local_params,
            local_indices: Vec::new(),
            block_codom: None,
            is_zero: None,
            is_nonzero: None,
            ind_consts: Vec::new(),
            rec_uparams: None,
            elim_level: None,
            k_target: None,
            majors: Vec::new(),
            motives: Vec::new(),
            minors: Vec::new(),
        }
    }
    fn is_nested(&self) -> bool { !self.nested_to_unspecialized_ty_nofvars.is_empty() }
}

#[derive(Debug, Clone)]
struct IndTyHeader<'a> {
    name: NamePtr<'a>,
    ty: ExprPtr<'a>,
    ctors: Vec<CtorHeader<'a>>,
}

#[derive(Debug, Clone, Copy)]
struct CtorHeader<'a> {
    name: NamePtr<'a>,
    ty: ExprPtr<'a>,
}

/// Condition 3:
///     assert that the first arguments being applied to the base `Const(..)`
///     in any given constructor are exactly the parameters required by the block.
///     In vernacular lean, we're used to just giving indices, but pretend everything
///     has an `@` prefix.
///     e.g.:
///     {A : Sort u}
///     for `@eq.refl A a a`
///     unfolds as (Const(eq, [u]), [A, a, a])
fn ctor_app_params_ok<'a>(ctor_apps: &[ExprPtr<'a>], local_params: &[ExprPtr<'a>]) -> bool {
    if ctor_apps.len() < local_params.len() {
        return false
    }

    for (app, param) in ctor_apps.iter().copied().zip(local_params.iter().copied()) {
        if app != param {
            return false
        }
    }
    true
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    fn specialize_nested(
        &mut self,
        t_from_file: &InductiveData<'t>,
        unmodified_tys_ctors: Vec<IndTyHeader<'t>>,
    ) -> InductiveCheckState<'t> {
        // Free variables for the block's paramters, and the instantiated end
        // of the telescope for the type being checked (the 0th type).
        let (local_params, _instd) = self.get_local_params(unmodified_tys_ctors[0].ty, t_from_file.num_params);

        let mut st = InductiveCheckState::new(
            t_from_file.info.uparams,
            u16::try_from(local_params.len()).unwrap(),
            unmodified_tys_ctors,
            local_params,
        );
        // Collect the new `NestedNewType` items constructed from any actually nested inductives.
        self.specialize_nested_aux(&mut st);

        // No stray free variables.
        for ind in st.all_inductives_incl_specialized.iter() {
            assert!(!self.ctx.read_expr(ind.ty).has_fvars());
            for c in ind.ctors.iter() {
                assert!(!self.ctx.read_expr(c.ty).has_fvars());
            }
        }
        st
    }

    /// This function does two important things, and it sort of needs to do them together.
    ///
    /// 1. it adds any new specialized inductive types needed to handle nested inductives to the state.
    /// For example, in the declaration for `Lean.Syntax`, adding `_nested.Array_X` to
    /// `st.all_inductives_incl_specialized`.
    ///
    /// 2. it goes through the constructors of all the inductives, including the newly added specialized
    /// ones, and finds instances of nested types, replacing them in with instances of the specialized types.
    /// For example, replacing the occurrence of `Array Syntax` in the `Lean.Syntax.node` constructor
    /// with `_nested.Array_N`.
    fn specialize_nested_aux(&mut self, st: &mut InductiveCheckState<'t>) {
        let mut i = 0usize;
        // `all_inductives_incl_specialized` begins as just the unmodified `IndTyHeader`
        // elements.
        //
        // Throughout the loop, calls to `replace_all_nested` may expand the list
        // of inductive type headers with new specialized types if this is a nested
        // inductive.
        while i < st.all_inductives_incl_specialized.len() {
            let mut new_ctors_for_i = Vec::new();
            for adjusted_ctor in (st.all_inductives_incl_specialized[i].clone()).ctors.iter() {
                let (ctor_local_params, ctor_type_instd) =
                    self.get_local_params(adjusted_ctor.ty, u16::try_from(st.local_params.len()).unwrap());
                let replaced_ctor_wo_params = self.replace_all_nested(ctor_type_instd, st, &ctor_local_params);
                let replaced_ctor_w_params =
                    self.ctx.abstr_pis(ctor_local_params.iter().copied(), replaced_ctor_wo_params);
                assert!(!self.ctx.read_expr(replaced_ctor_w_params).has_fvars());
                // Push the constructor with the params put back, free variables abstracted,
                // and ococurrences of nested inductives replaced with specialized types.
                new_ctors_for_i.push(CtorHeader { name: adjusted_ctor.name, ty: replaced_ctor_w_params });
            }
            // update the constructors for the inductive `i` with the replaced constructors.
            match st.all_inductives_incl_specialized.get_mut(i) {
                // e.g. replace the base `Syntax.node` with the updated one that replaces `Array`.
                Some(old) => {
                    let _ = std::mem::replace(&mut old.ctors, new_ctors_for_i);
                }
                None => panic!("inductive type {} is missing", i),
            }
            i += 1;
        }

        st.nested_to_unspecialized_ty_nofvars = {
            let mut out = crate::util::new_fx_index_map();
            for (n, e) in st.nested_to_unspecialized_ty_wfvars.iter() {
                let e = self.ctx.abstr(*e, st.local_params.as_slice());
                out.insert(*n, e);
            }
            out
        };
    }

    /// Return a sequence of expressions which are free variables corresponding to the
    /// inductive type's parameters, also returning the end of the telescope instantiated
    /// with the parameters.
    fn get_local_params(&mut self, mut e: ExprPtr<'t>, num_params: u16) -> (Vec<ExprPtr<'t>>, ExprPtr<'t>) {
        let mut param_locals = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            match self.ctx.read_expr(e) {
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    e = self.ctx.inst(body, &[local_]);
                    e = self.whnf(e);
                    param_locals.push(local_);
                }
                _ => panic!("exhausted telescope early"),
            }
        }
        (param_locals, e)
    }

    /// Check the 0th element of the list of inductive types; this one is different
    /// than the mutuals, because we need to determine the target for the block codom
    /// and some other stuff.
    fn check_inductive_spec_0th(&mut self, uparams: LevelsPtr<'t>, st: &mut InductiveCheckState<'t>) {
        self.tc_cache.clear();
        let (ind_name, mut ind_ty_cursor) = st.all_inductives_incl_specialized.get(0).map(|x| (x.name, x.ty)).unwrap();
        ind_ty_cursor = self.whnf(ind_ty_cursor);
        let mut indices_locals = Vec::new();
        let mut i = 0;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ind_ty_cursor) {
            if i < st.local_params.len() {
                let local_ = st.local_params[i];
                match self.ctx.read_expr(local_) {
                    Local { binder_type: t2, .. } => {
                        self.tc_cache.clear();
                        self.assert_def_eq(binder_type, t2);
                    }
                    _ => panic!(),
                }
                ind_ty_cursor = self.ctx.inst(body, &[st.local_params[i]]);
                ind_ty_cursor = self.whnf(ind_ty_cursor);
            } else {
                let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                ind_ty_cursor = self.ctx.inst(body, &[local_]);
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                indices_locals.push(local_)
            }
            i += 1;
        }
        let block_codom = self.ensure_sort(ind_ty_cursor);
        let is_nonzero = self.ctx.is_nonzero(block_codom);
        let is_zero = self.ctx.is_zero(block_codom);
        let ind_const = self.ctx.mk_const(ind_name, uparams);

        st.local_indices.push(indices_locals);
        st.block_codom = Some(block_codom);
        st.is_zero = Some(is_zero);
        st.is_nonzero = Some(is_nonzero);
        st.ind_consts.push(ind_const);
    }

    /// Check the rest of the types in a mutual block, ensuring they agree with the base type.
    fn check_inductive_specs_mutual1(&mut self, st: &mut InductiveCheckState<'t>, ind: IndTyHeader<'t>) {
        self.tc_cache.clear();
        let mut ind_ty_cursor = self.whnf(ind.ty);
        let mut indices_locals = Vec::new();
        let mut i = 0;
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ind_ty_cursor) {
            if i < st.local_params.len() {
                ind_ty_cursor = self.ctx.inst(body, &[st.local_params[i]]);
                ind_ty_cursor = self.whnf(ind_ty_cursor);
            } else {
                let local_ = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                ind_ty_cursor = self.ctx.inst(body, &[local_]);
                ind_ty_cursor = self.whnf(ind_ty_cursor);
                indices_locals.push(local_)
            }
            i += 1;
        }
        let codom_level = self.ensure_sort(ind_ty_cursor);
        assert!(self.ctx.eq_antisymm(codom_level, st.block_codom.unwrap()));
        st.local_indices.push(indices_locals);
        st.ind_consts.push(self.ctx.mk_const(ind.name, st.uparams));
    }

    /// This starts by receiving the "full" `InductiveType` specification from the export
    /// file for the actual declaration being checked. It *ALSO* gets the NestedInductiveState,
    /// since the process of checking these also has to deal with the new types created
    /// during the nest procedure.
    fn check_inductive_specs(&mut self, st: &mut InductiveCheckState<'t>) {
        let nbefore = st.all_inductives_incl_specialized.len();
        for i in 0..st.all_inductives_incl_specialized.len() {
            if i == 0 {
                self.check_inductive_spec_0th(st.uparams, st);
                assert_eq!(st.local_indices.len(), 1);
            } else {
                assert_eq!(st.local_indices.len(), i);
                self.check_inductive_specs_mutual1(st, st.all_inductives_incl_specialized[i].clone());
            }
        }
        assert_eq!(st.all_inductives_incl_specialized.len(), nbefore);
        assert_eq!(st.all_inductives_incl_specialized.len(), st.local_indices.len());
    }

    fn is_nested_ind_app(&mut self, st: &InductiveCheckState<'t>, e: ExprPtr<'t>) -> Option<InductiveData<'t>> {
        if !(matches!(self.ctx.read_expr(e), App { .. })) {
            return None
        }
        let (_f, name, _levels, args) = self.ctx.unfold_const_apps(e)?;
        // If this is an application of an inductive, like `Array A`
        let ind_ty_declar @ InductiveData { num_params, .. } = self.env.get_inductive(&name)?;
        if (*num_params as usize) > args.len() {
            return None
        }
        let mut loose_bvars = false;
        let mut is_nested = false;
        for i in 0..(*num_params as usize) {
            let this_param = args[i];
            if self.ctx.num_loose_bvars(this_param) != 0 {
                loose_bvars = true;
            }
            if self
                .ctx
                .find_const(this_param, |n| st.all_inductives_incl_specialized.iter().any(|new_ty| new_ty.name == n))
            {
                is_nested = true;
            }
        }
        if !is_nested {
            return None
        }
        if loose_bvars {
            panic!("nested types cannot contain locals (loose bvars found)")
        }
        Some(ind_ty_declar.clone())
    }

    fn header_of_ty(&self, t: &InductiveData<'t>) -> IndTyHeader<'t> {
        fn header_of_ctor<'t>(t: &ConstructorData<'t>) -> CtorHeader<'t> {
            CtorHeader { name: t.info.name, ty: t.info.ty }
        }
        let ctors = {
            let mut out = Vec::new();
            for ctor_name in t.all_ctor_names.as_ref() {
                out.push(header_of_ctor(self.env.get_constructor(ctor_name).unwrap()));
            }
            out
        };
        IndTyHeader { name: t.info.name, ty: t.info.ty, ctors }
    }

    /// For some exported inductive declaration `T` that has a list of mutual names
    /// `[T, U, .., Z]`, return the `IndTyHeader` elements for `[T, U, .., Z]`, without
    /// any specializations/modifications.
    fn collect_unmodified_mutuals(&self, t_from_file: &InductiveData<'t>) -> Vec<IndTyHeader<'t>> {
        let mut all_inductives = Vec::new();
        // Get all of the mutual inductives, but don't re-insert the base type.
        for n in t_from_file.all_ind_names.iter() {
            let t = self.env.get_inductive(n).unwrap();
            all_inductives.push(self.header_of_ty(t));
        }
        all_inductives
    }

    fn mk_unique_name(&mut self, n: NamePtr<'t>, st: &mut InductiveCheckState<'t>) -> NamePtr<'t> {
        for idx in st.next_ngen_idx..u64::MAX {
            let tester = self.ctx.append_index_after(n, idx);
            if !self.env.declars.contains_key(&tester) {
                st.next_ngen_idx = idx + 1;
                return tester
            }
        }
        panic!("Unable to generate unique name, u64 exhausted")
    }

    /// *THIS METHOD MAY PUSH NEW SPECIALIZED INDUCTIVES TO THE STATE*
    ///
    /// `e` is a constructor or part of some constructor for an inductive or specialized inductive
    /// in this block.
    ///
    /// `outgoing_param_locals` are the free variables for the parameters taken
    /// from the constructor's telescope.
    ///
    /// if `e` is a nested occurrence/application, like the `Array Syntax` argument to
    /// the `Lean.Syntax.node` constructor, replace `Array Syntax` with `_nested.Array_X`.
    fn replace_if_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        // If this has been called with the constructor for an unspecialized version of a nested
        // type, for example called with `Array.mk`, the outgoing_param will be a free variable
        // of carrier type `A`, which should be replaced with whatever is being nested, like `Lean.Syntax`.
        outgoing_param_locals: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        // Using the `Lean.Syntax.node` constructor as an example, if `e` is the application of
        // `Array Lean.Syntax`, this variable will be the base declaration for `Array`.
        let nested_container_ty = self.is_nested_ind_app(st, e)?;
        // Get the `Array` from `Array Syntax`
        let (f, i_name, i_levels, args) = self.ctx.unfold_const_apps(e).unwrap();
        assert!(nested_container_ty.num_params as usize <= args.len());
        // Reapply the portion of the unfolded applications that is the parameters.
        let i_as = self.ctx.foldl_apps(f, args.iter().copied().take(nested_container_ty.num_params as usize));
        // Application of the type to the swapped out fvar params
        let i_params = self.ctx.replace_params(i_as, st.local_params.as_slice(), outgoing_param_locals);

        // E.g. `_nested.List_1` |-> `List (Sexpr #(A : Sort(u + 1)))`
        if let Some((aux_i_name, _)) =
            st.nested_to_unspecialized_ty_wfvars.iter().find(|(_name, expr)| **expr == i_params)
        {
            let f = self.ctx.mk_const(*aux_i_name, st.uparams);
            let f = self.ctx.foldl_apps(f, outgoing_param_locals.iter().copied());
            let f =
                self.ctx.foldl_apps(f, (args[(nested_container_ty.num_params as usize)..args.len()]).iter().copied());
            Some(f)
        } else {
            let mut result: Option<ExprPtr> = None;
            // `Array`, `List`, and any mutuals in the appropriate block etc.
            for nested_container_name in nested_container_ty.all_ind_names.iter().copied() {
                // The inductive declaration for the container type, like `Array`
                let InductiveData { info: container_ty_info, all_ctor_names: all_nested_container_ctor_names, .. } =
                    self.env.get_inductive(&nested_container_name)?;
                // `i_levels` is the set of uparams we actually found in the declaration we're checking,
                // so the set of uparams in `Lean.Syntax`, as opposed to the uparam declars for `Array`
                let js = {
                    let base_const = self.ctx.mk_const(nested_container_name, i_levels);
                    self.ctx.foldl_apps(base_const, (args[0..nested_container_ty.num_params as usize]).iter().copied())
                };

                // Example: From `Array`, make `_nested.Array_1`
                let aux_nested_container_name = {
                    let nested_pfx = self.ctx.str1("_nested");
                    let base = self.ctx.concat_name(nested_pfx, nested_container_name);
                    self.mk_unique_name(base, st)
                };
                // Replace the telescope on the auxiliary declaration to match the declaration
                // we're currently checking. Can also add parameters as needed.
                let nested_container_aux_type = {
                    let base = self.ctx.subst_expr_levels(container_ty_info.ty, container_ty_info.uparams, i_levels);
                    let instd =
                        self.ctx.inst_forall_params(base, nested_container_ty.num_params as usize, args.as_slice());
                    let out = self.ctx.abstr_pis(outgoing_param_locals.iter().copied(), instd);
                    out
                };
                let jsprime = self.ctx.replace_params(js, st.local_params.as_slice(), outgoing_param_locals);
                st.nested_to_unspecialized_ty_wfvars.insert(aux_nested_container_name, jsprime);
                if nested_container_name == i_name {
                    let f = self.ctx.mk_const(aux_nested_container_name, st.uparams);
                    let f = self.ctx.foldl_apps(f, outgoing_param_locals.iter().copied());
                    let args = &args[nested_container_ty.num_params as usize..args.len()];
                    let f = self.ctx.foldl_apps(f, args.iter().copied());
                    result = Some(f);
                }
                let mut auxj_ctors = Vec::<CtorHeader>::new();
                for j_ctor_name in all_nested_container_ctor_names.iter().copied() {
                    let ConstructorData { info: j_ctor_info, .. } = self.env.get_constructor(&j_ctor_name)?;
                    // Replace `Array.mk` with `_nested.Array_2.mk`
                    let auxj_ctor_name =
                        self.ctx.replace_pfx(j_ctor_name, nested_container_name, aux_nested_container_name);
                    let auxj_ctor_type = self.ctx.subst_expr_levels(j_ctor_info.ty, j_ctor_info.uparams, i_levels);
                    let auxj_ctor_type = self.ctx.inst_forall_params(
                        auxj_ctor_type,
                        nested_container_ty.num_params as usize,
                        args.as_slice(),
                    );
                    let auxj_ctor_type = self.ctx.abstr_pis(outgoing_param_locals.iter().copied(), auxj_ctor_type);
                    auxj_ctors.push(CtorHeader { name: auxj_ctor_name, ty: auxj_ctor_type })
                }
                st.all_inductives_incl_specialized.push(IndTyHeader {
                    name: aux_nested_container_name,
                    ty: nested_container_aux_type,
                    ctors: auxj_ctors,
                });
            }
            result
        }
    }

    fn replace_all_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        outgoing_params: &Vec<ExprPtr<'t>>,
    ) -> ExprPtr<'t> {
        // Try to replace locally before traversing into the lower parts.
        if let Some(eprime) = self.replace_if_nested(e, st, outgoing_params) {
            eprime
        } else {
            match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | Local { .. } | NatLit { .. } | StringLit { .. } => e,
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, outgoing_params);
                    let val = self.replace_all_nested(val, st, outgoing_params);
                    let body = self.replace_all_nested(body, st, outgoing_params);
                    self.ctx.mk_let(binder_name, binder_type, val, body)
                }
                App { fun, arg, .. } => {
                    let fun = self.replace_all_nested(fun, st, outgoing_params);
                    let arg = self.replace_all_nested(arg, st, outgoing_params);
                    self.ctx.mk_app(fun, arg)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.replace_all_nested(structure, st, outgoing_params);
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
            }
        }
    }

    // This is only ONE of the binders from the constructor's telescope,
    // AFTER the block params have been removed. These are the "proper"
    // constructor arguments.
    //
    // When we match here on Pi { n, t, s, b }, `t` is the left hand side
    // of a function argument to an inductive constructor.
    // We need to search `t` to prevent non-positive occurrences; the following
    // would be prohibited:
    //
    //```ignore
    // inductive Foo
    // | mk (f : Foo → Nat) : Foo
    //```
    //
    // Read about issues with non-positive occurrences here:
    // https://counterexamples.org/strict-positivity.html?highlight=posi#positivity-strict-and-otherwise
    fn check_positivity1(&mut self, st: &InductiveCheckState<'t>, mut ctor_type_cursor: ExprPtr<'t>) {
        loop {
            ctor_type_cursor = self.whnf(ctor_type_cursor);
            match self.ctx.read_expr(ctor_type_cursor) {
                _any if !self.has_ind_occ(ctor_type_cursor, st.ind_consts.as_ref()) => return,
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    if self.has_ind_occ(binder_type, st.ind_consts.as_ref()) {
                        panic!("non-positive occurrence");
                    }
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    ctor_type_cursor = self.ctx.inst(body, &[local]);
                }
                _ => {
                    // We only need to know that it's a valid ind-app for SOMETHING in the block, since
                    // this is only a binder in the constructor, not the end of the telescope.
                    assert!(self.which_valid_ind_app(st, ctor_type_cursor).is_some());
                    return;
                }
            }
        }
    }

    /// Check whether `ind_ty_app` is a valid application of some arguments
    /// to `parent_ind_const`. The arguments need to be the parameters for the
    /// inductive block.
    fn is_valid_ind_app(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        ind_ty_app: ExprPtr<'t>,
    ) -> bool {
        // The arguments applied to the constructor are the params + indices.
        let (base_const, ctor_apps) = self.ctx.unfold_apps(ind_ty_app);
        let ind_name = match self.ctx.read_expr(base_const) {
            Const { name, .. } if name == parent_ind_name => name,
            _ => return false,
        };
        let ind_name_pos = st
            .ind_consts
            .iter()
            .copied()
            .position(|x| match self.ctx.read_expr(x) {
                Const { name, .. } => name == ind_name,
                _ => panic!(),
            })
            .unwrap();
        let ind_name_num_indices = st.local_indices[ind_name_pos].len();

        if ctor_apps.len() != (st.local_params.len() + ind_name_num_indices) {
            return false
        }
        ctor_app_params_ok(ctor_apps.as_slice(), st.local_params.as_slice())
    }

    // For an expression `E` and a list
    // of names `NS`, recursively search through `E` for a `Const { name, levels }`
    // `C`, whose name is ANY of the names in `NS`. If such a `C` exists,
    // return true, else return false.
    //
    // This is used in the formation of inductive types, to determine whether
    // a type is recursive, reflexive, contains only positive occurrences, and
    // has only valid applications.
    fn has_ind_occ(&mut self, e: ExprPtr<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        let f = |nptr| {
            haystack.iter().copied().any(|c| match self.ctx.read_expr(c) {
                Const { name, .. } => name == nptr,
                _ => panic!(),
            })
        };

        self.ctx.find_const(e, f)
    }

    /// For some application of arguments to an inductive type (e.g. `Eq A a`), get back
    /// the applied indices, and the index showing which inductive type from the block
    /// is being applied to.
    fn get_i_indices(&mut self, st: &InductiveCheckState<'t>, ind_ty_app: ExprPtr<'t>) -> (usize, Vec<ExprPtr<'t>>) {
        let valid_app_idx = self.which_valid_ind_app(st, ind_ty_app).unwrap();
        let (_, mut ctor_args_wo_params) = self.ctx.unfold_apps_stack(ind_ty_app);
        // Compensate for stack-like unfold
        for _ in 0..st.local_params.len() {
            ctor_args_wo_params.pop();
        }
        (valid_app_idx, ctor_args_wo_params)
    }

    /// For some expression `e`, get the index of the inductive type
    /// that `e` is a valid application of.
    fn which_valid_ind_app(&mut self, st: &InductiveCheckState<'t>, u_i_ty: ExprPtr<'t>) -> Option<usize> {
        // For every inductive type in the block...
        for (i, ind_const) in st.ind_consts.iter().copied().enumerate() {
            let ind_name = match self.ctx.read_expr(ind_const) {
                Const { name, .. } => name,
                _ => panic!(),
            };
            if self.is_valid_ind_app(st, ind_name, u_i_ty) {
                return Some(i)
            }
        }
        None
    }

    pub(crate) fn check_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        mut ctor_type_cursor: ExprPtr<'t>,
    ) {
        self.tc_cache.clear();
        for i in 0..st.local_params.len() {
            let local_param = st.local_params[i];
            match self.ctx.read_expr_pair(ctor_type_cursor, local_param) {
                (Pi { binder_type, body, .. }, Local { binder_type: local_type, .. }) => {
                    self.assert_def_eq(binder_type, local_type);
                    ctor_type_cursor = self.ctx.inst(body, &[local_param]);
                }
                _ => panic!(),
            }
        }
        // Non-param constructor args.
        while let Pi { binder_name, binder_type, binder_style, body, .. } = self.ctx.read_expr(ctor_type_cursor) {
            let s = self.ensure_infers_as_sort(binder_type);
            // The inductive being constructed either has to be a `Prop`,
            // or the constructor argument's type has to be <= the inductive's
            // type.
            if !(st.is_zero.unwrap() || self.ctx.leq(s, st.block_codom.unwrap())) {
                panic!("Constructor argument was too large for the corresponding inductive type")
            }

            // Assert that there are no non-positive occurrences in the constructor.
            self.check_positivity1(st, binder_type);
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            ctor_type_cursor = self.ctx.inst(body, &[local]);
        }
        // The end of the constructor has to be of the form `parentIndConst params* indices*`
        // as in `List A` or `Nat.le x y`
        assert!(self.is_valid_ind_app(st, parent_ind_name, ctor_type_cursor))
    }

    // Test large elimination for an inductive that we know is...
    // 1. An inductive predicate (is in `Prop`)
    // 1. Not a mutual inductive
    // 3. Has exactly one constructor.
    //
    // This kind of inductive prop is okay for large elimination IFF every
    // non-prop ctor arg is a param or index of the inductive type.
    //
    // Example: This inductive prop is okay for large elimination, because `n` is an index.
    //```
    // inductive MyTypeLarge (A : Type) : Nat → Prop
    // | mk (n : Nat) : MyTypeLarge A n
    // ```
    //
    // This type is not okay for large elimination, because `m` is neither a parameter nor an index.
    //```
    // inductive MyTypeSmall (A : Type) : Nat → Prop
    // | mk (m : Nat) (n : Nat) : MyTypeSmall A n
    //```
    fn large_elim_test_aux(&mut self, mut ctor_type_cursor: ExprPtr<'t>, mut rem_params: usize) -> bool {
        self.tc_cache.clear();
        let mut non_prop_ctor_telescope_elems = Vec::new();
        loop {
            match self.ctx.read_expr(ctor_type_cursor) {
                Pi { binder_name, binder_style, binder_type, body, .. } if rem_params != 0 => {
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    ctor_type_cursor = self.ctx.inst(body, &[local]);
                    rem_params -= 1;
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    ctor_type_cursor = self.ctx.inst(body, &[local]);
                    let binder_type_level = self.ensure_infers_as_sort(binder_type);
                    // If the binder type is NOT in sort 0, add it to the list
                    // of constructor args that need to be checked
                    if !self.ctx.is_zero(binder_type_level) {
                        non_prop_ctor_telescope_elems.push(local);
                    }
                }
                _ => break,
            }
        }

        let (_, ind_ty_params_and_indices) = self.ctx.unfold_apps(ctor_type_cursor);

        // Check whether `non_prop_ctor_telescope_elems` is a subset of
        // `ind_ty params ++ ind_ty indices`
        //
        // if the list of non-prop constructor args is NOT a subset of
        // the exprs being applied to the inductive (which is params + indices)
        // then we can say that this type only eliminates into Prop/Sort 0
        non_prop_ctor_telescope_elems.iter().all(|arg| ind_ty_params_and_indices.contains(arg))
    }

    fn large_elim_test(&mut self, st: &InductiveCheckState<'t>) -> bool {
        if st.is_nonzero.unwrap() {
            // If our inductive is in `Type <n>`, it's large eliminating
            return true
        }

        match st.all_inductives_incl_specialized.as_slice() {
            [] => panic!("inductive declaration with no types declared"),
            [ind_ty] => {
                match ind_ty.ctors.as_slice() {
                    // This type is an empty prop (has no constructors)
                    [] => true,
                    // At this point, we know that we're dealing with an inductive that...
                    // 1. is not a mutual inductive (ind_types = 1)
                    // 2. is an inductive proposition (because its result sort is Prop/0)
                    // 3. has one and only one constructor
                    [ctor] => self.large_elim_test_aux(ctor.ty, st.local_params.len()),
                    // More than one constructor; no large elimination.
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn gen_elim_level(&mut self, st: &InductiveCheckState<'t>) -> NamePtr<'t> {
        let p = self.ctx.str1("u");
        if !self.ctx.contains_param(st.uparams, p) {
            return p
        }
        // Lean's pretty printer starts at 1 for universes.
        let mut i = 1u64;
        loop {
            let candidate = self.ctx.append_index_after(p, i);
            if self.ctx.contains_param(st.uparams, candidate) {
                i += 1;
            } else {
                return candidate
            }
        }
    }

    fn mk_elim_level(&mut self, st: &mut InductiveCheckState<'t>) {
        if self.large_elim_test(st) {
            let elim_level = self.gen_elim_level(st);
            let elim_level = self.ctx.param(elim_level);
            // Extra work since you want the new thing at the front of the vector (in position 0)
            let rec_levels = {
                let mut base = vec![elim_level];
                for l in self.ctx.read_levels(st.uparams).iter().copied() {
                    base.push(l)
                }
                self.ctx.alloc_levels(Arc::from(base))
            };
            st.rec_uparams = Some(rec_levels);
            st.elim_level = Some(elim_level);
        } else {
            // If this is not a large eliminating type, the elim level can only be zero,
            // and the only uparams for the recursor are those of the inductive spec.
            st.elim_level = Some(self.ctx.zero());
            st.rec_uparams = Some(st.uparams);
        };
    }

    /// To be a target for k-like reduction, a type cannot be mutual or nested, must be an inductive
    /// prop, must have only one constructor, and the constructor can take only the type's parameters
    /// as arguments.
    fn init_k_target(&mut self, st: &mut InductiveCheckState<'t>) {
        let is_k_target = st.is_zero.unwrap()
            && st.all_inductives_incl_specialized.len() == 1
            && match st.all_inductives_incl_specialized[0].ctors.as_slice() {
                [only_ctor] => self.ctx.pi_telescope_size(only_ctor.ty) as usize == st.local_params.len(),
                _ => false,
            };
        st.k_target = Some(is_k_target);
    }

    fn mk_majors(&mut self, st: &mut InductiveCheckState<'t>) {
        for (idx, ind_const) in st.ind_consts.iter().copied().enumerate() {
            let mut ty = self.ctx.foldl_apps(ind_const, st.local_params.iter().copied());
            ty = self.ctx.foldl_apps(ty, st.local_indices[idx].iter().copied());
            let t = self.ctx.str1("t");
            st.majors.push(self.ctx.mk_unique(t, BinderStyle::Default, ty));
        }
    }

    fn mk_motive_dep(&mut self, st: &InductiveCheckState<'t>, major: ExprPtr<'t>, ind_type_idx: u64) -> ExprPtr<'t> {
        let elim_sort = self.ctx.mk_sort(st.elim_level.unwrap());
        let w_major = self.ctx.abstr_pi(major, elim_sort);
        let motive_type = self.ctx.abstr_pi_telescope(&st.local_indices[ind_type_idx as usize], w_major);
        let motive_name_base = self.ctx.str1("motive");
        let motive_name = if st.all_inductives_incl_specialized.len() > 1 {
            // Lean uses 1-based indexing for these, so we try to match for the pretty printer output.
            self.ctx.append_index_after(motive_name_base, ind_type_idx + 1)
        } else {
            motive_name_base
        };

        self.ctx.mk_unique(motive_name, BinderStyle::Implicit, motive_type)
    }

    fn mk_motives(&mut self, st: &mut InductiveCheckState<'t>) {
        debug_assert_eq!(st.local_indices.len(), st.ind_consts.len());
        debug_assert_eq!(st.majors.len(), st.ind_consts.len());
        for i in 0..st.ind_consts.len() {
            let major = st.majors[i];
            st.motives.push(self.mk_motive_dep(st, major, i as u64));
        }
    }

    fn is_rec_argument(&mut self, st: &InductiveCheckState<'t>, mut ctor_btype_cursor: ExprPtr<'t>) -> Option<usize> {
        ctor_btype_cursor = self.whnf(ctor_btype_cursor);
        if let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ctor_btype_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            ctor_btype_cursor = self.ctx.inst(body, &[local]);
            self.is_rec_argument(st, ctor_btype_cursor)
        } else {
            self.which_valid_ind_app(st, ctor_btype_cursor)
        }
    }

    fn handle_rec_args_aux(&mut self, mut rec_arg_cursor: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut xs = Vec::new();
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(rec_arg_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            rec_arg_cursor = self.ctx.inst(body, &[local]);
            rec_arg_cursor = self.whnf(rec_arg_cursor);
            xs.push(local)
        }
        (rec_arg_cursor, xs)
    }

    fn sep_nonrec_rec_ctor_args(
        &mut self,
        st: &InductiveCheckState<'t>,
        mut ctor_type_cursor: ExprPtr<'t>,
        rem_params: &[ExprPtr<'t>],
    ) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>, Vec<ExprPtr<'t>>) {
        let mut all_args = Vec::new();
        let mut rec_args = Vec::new();
        self.tc_cache.clear();
        for i in 0..st.local_params.len() {
            match (self.ctx.read_expr(ctor_type_cursor), rem_params[i]) {
                (Pi { body, .. }, local_param) => {
                    ctor_type_cursor = self.ctx.inst(body, &[local_param]);
                }
                _ => panic!(),
            }
        }
        while let Pi { binder_name, binder_style, binder_type, body, .. } = self.ctx.read_expr(ctor_type_cursor) {
            let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
            ctor_type_cursor = self.ctx.inst(body, &[local]);
            all_args.push(local);
            if self.is_rec_argument(st, binder_type).is_some() {
                rec_args.push(local);
            }
        }
        (ctor_type_cursor, all_args, rec_args)
    }

    fn handle_rec_args_minor(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor_idx: usize,
        rec_args: &[ExprPtr<'t>],
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        for (i, rec_arg) in rec_args.iter().copied().enumerate() {
            self.tc_cache.clear();
            let u_i_ty = self.whnf_after_infer(rec_arg, crate::tc::InferFlag::InferOnly);
            let (arg_ty, xs) = self.handle_rec_args_aux(u_i_ty);
            let (ind_ty_idx, applied_indices) = self.get_i_indices(st, arg_ty);
            let motive = st.motives.get(ind_ty_idx).copied().expect("Failed to get specified motive");
            let motive_base = {
                let lhs = self.ctx.foldl_apps(motive, applied_indices.into_iter().rev());
                let u_app = self.ctx.foldl_apps(rec_arg, xs.iter().copied());
                self.ctx.mk_app(lhs, u_app)
            };
            let v_i_ty = self.ctx.abstr_pis(xs.iter().copied(), motive_base);
            let v_name = self.ctx.str1("v");
            // rec_arg often has a hygienic name
            let v_name = self.ctx.append_index_after(v_name, ctor_idx as u64);
            let v_name = self.ctx.append_index_after(v_name, i as u64);
            let v_i = self.ctx.mk_unique(v_name, BinderStyle::Default, v_i_ty);
            out.push(v_i);
        }
        out
    }

    fn mk_minors1group(&mut self, st: &InductiveCheckState<'t>, ctors: &[CtorHeader<'t>]) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        for (ctor_idx, ctor) in ctors.iter().copied().enumerate() {
            let (stripd_instd_ctor_type, all_ctor_args, rec_ctor_args) =
                self.sep_nonrec_rec_ctor_args(st, ctor.ty, st.local_params.as_slice());
            let (ind_ty_idx, applied_indices) = self.get_i_indices(st, stripd_instd_ctor_type);
            let motive = st.motives.get(ind_ty_idx).copied().expect("Failed to get specified motive");
            let c_app0 = {
                let rhs = self.ctx.mk_const(ctor.name, st.uparams);
                let rhs = self.ctx.foldl_apps(rhs, st.local_params.iter().copied());
                self.ctx.foldl_apps(rhs, all_ctor_args.iter().copied())
            };
            let c_app = self.ctx.foldl_apps(motive, applied_indices.into_iter().rev());
            let c_app = self.ctx.mk_app(c_app, c_app0);
            let v = self.handle_rec_args_minor(st, ctor_idx, rec_ctor_args.as_slice());

            let minor_type = self.ctx.abstr_pis(v.iter().copied(), c_app);
            let minor_type = self.ctx.abstr_pis(all_ctor_args.iter().copied(), minor_type);
            let minor_name = match self.ctx.read_name(ctor.name) {
                // Use the constructor's name if it's available;
                crate::name::Name::Str(_, sfx, _) => self.ctx.str(self.ctx.anonymous(), sfx),
                // If the constructor name isn't available for some reason, use a generic one
                _ => {
                    let minor_name = self.ctx.str1("m");
                    self.ctx.append_index_after(minor_name, ctor_idx as u64)
                }
            };
            let minor = self.ctx.mk_unique(minor_name, BinderStyle::Default, minor_type);
            out.push(minor);
        }
        out
    }

    fn mk_minors(&mut self, st: &mut InductiveCheckState<'t>) {
        assert_eq!(st.all_inductives_incl_specialized.len(), st.ind_consts.len());
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            st.minors.push(self.mk_minors1group(st, ind_ty.ctors.as_slice()))
        }
    }

    fn handle_rec_ctor_args_rec_rule(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_ctor_args: &[ExprPtr<'t>],
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
        let flat_mapped_minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
        for rec_ctor_arg in rec_ctor_args.iter().copied() {
            self.tc_cache.clear();
            let u_i_ty = self.whnf_after_infer(rec_ctor_arg, InferFlag::InferOnly);
            let (u_i_ty, xs) = self.handle_rec_args_aux(u_i_ty);
            let (it_idx, applied_indices) = self.get_i_indices(st, u_i_ty);
            let it_name = st.all_inductives_incl_specialized.get(it_idx).map(|x| x.name).unwrap();
            let rec_name = self.ctx.str(it_name, rec_str_ptr);
            let rec_app = self.ctx.mk_const(rec_name, st.rec_uparams.unwrap());
            let app = self.ctx.foldl_apps(rec_app, st.local_params.iter().copied());
            let app = self.ctx.foldl_apps(app, st.motives.iter().copied());
            let app = self.ctx.foldl_apps(app, flat_mapped_minors.iter().copied());
            let app = self.ctx.foldl_apps(app, applied_indices.iter().copied().rev());
            let app_rhs = self.ctx.foldl_apps(rec_ctor_arg, xs.iter().copied());
            let app = self.ctx.mk_app(app, app_rhs);
            let v_hd = self.ctx.abstr_lambda_telescope(xs.as_slice(), app);
            out.push(v_hd);
        }
        out
    }

    fn mk_rec_rule1(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor: CtorHeader<'t>,
        flat_mapped_minors: &[ExprPtr<'t>],
        this_minor: ExprPtr<'t>,
    ) -> RecRule<'t> {
        let (_, all_ctor_args, rec_ctor_args) = self.sep_nonrec_rec_ctor_args(st, ctor.ty, st.local_params.as_slice());
        let handled_rec_args = self.handle_rec_ctor_args_rec_rule(st, rec_ctor_args.as_slice());
        let comp_rhs = self.ctx.foldl_apps(this_minor, all_ctor_args.iter().copied());
        let comp_rhs = self.ctx.foldl_apps(comp_rhs, handled_rec_args.iter().copied());
        let comp_rhs = self.ctx.abstr_lambda_telescope(all_ctor_args.as_slice(), comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(flat_mapped_minors, comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(st.motives.as_slice(), comp_rhs);
        let comp_rhs = self.ctx.abstr_lambda_telescope(st.local_params.as_slice(), comp_rhs);
        let num_fields = self.ctx.pi_telescope_size(ctor.ty) as usize - st.local_params.len();
        RecRule {
            ctor_name: ctor.name,
            ctor_telescope_size_wo_params: u16::try_from(num_fields).unwrap(),
            val: comp_rhs,
        }
    }

    fn mk_rec_rules(&mut self, st: &InductiveCheckState<'t>) -> Vec<Vec<RecRule<'t>>> {
        let mut rec_rules = Vec::new();
        let minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
        let mut overall_ctor_idx = 0;
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            let mut grp = Vec::new();
            for ctor in ind_ty.ctors.iter().copied() {
                let this_minor = minors[overall_ctor_idx];
                let rec_rule = self.mk_rec_rule1(st, ctor, minors.as_slice(), this_minor);
                overall_ctor_idx += 1;
                grp.push(rec_rule);
            }
            rec_rules.push(grp);
        }
        rec_rules
    }

    // Assert that the inductive types being added to the extension which
    // are also in the export file are definitionally equal.
    fn assert_nonnested_tys_def_eq(&mut self, base_ind: &InductiveData<'t>, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for name in base_ind.all_ind_names.iter() {
            match (self.env.get_old_declar(name), self.env.get_temp_declar(name)) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }
        }
    }

    fn assert_nonnested_ctors_def_eq(&mut self, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for inductive in st.all_inductives_incl_specialized.iter() {
            for ctor in inductive.ctors.iter() {
                match (self.env.get_old_declar(&ctor.name), self.env.get_temp_declar(&ctor.name)) {
                    (Some(Declar::Constructor(old)), Some(Declar::Constructor(new))) => {
                        debug_assert!(!std::ptr::eq(old, new));
                        self.tc_cache.clear();
                        self.assert_def_eq(old.info.ty, new.info.ty);
                    }
                    _ => panic!(),
                }
            }
        }
    }

    fn assert_nonnested_rec_rule_def_eq(
        &mut self,
        st: &InductiveCheckState<'t>,
        old: LevelsPtr<'t>,
        imported_rr: &RecRule<'t>,
        constructed_rr: &RecRule<'t>,
    ) {
        assert!(!st.is_nested());
        self.tc_cache.clear();
        assert_eq!(imported_rr.ctor_name, constructed_rr.ctor_name);
        assert_eq!(imported_rr.ctor_telescope_size_wo_params, constructed_rr.ctor_telescope_size_wo_params);
        let rr_made_val = self.ctx.subst_expr_levels(constructed_rr.val, st.rec_uparams.unwrap(), old);
        self.assert_def_eq(imported_rr.val, rr_made_val);
    }

    fn assert_nonnested_recursors_def_eq(&mut self, st: &InductiveCheckState<'t>, recursors: &Vec<Declar<'t>>) {
        assert!(!st.is_nested());
        for new_rec in recursors {
            match self.env.get_old_declar(&new_rec.info().name) {
                Some(reference @ Declar::Recursor(RecursorData { info, rec_rules, .. })) => {
                    let rec_ty = self.ctx.subst_expr_levels(info.ty, st.rec_uparams.unwrap(), reference.info().uparams);
                    assert_eq!(rec_rules.len(), rec_rules.len());
                    for (r_old, r_new) in rec_rules.iter().zip(rec_rules.iter()) {
                        self.assert_nonnested_rec_rule_def_eq(st, reference.info().uparams, r_old, r_new)
                    }
                    self.tc_cache.clear();
                    self.assert_def_eq(reference.info().ty, rec_ty);
                }
                #[allow(clippy::needless_return)]
                _ => return,
            };
        }
    }

    fn mk_recursor_aux(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_name: NamePtr<'t>,
        motive: ExprPtr<'t>,
        major: ExprPtr<'t>,
        local_indices: &[ExprPtr<'t>],
        flat_mapped_minors: &[ExprPtr<'t>],
        rec_rules: &[RecRule<'t>],
    ) -> Declar<'t> {
        let motive_app_base = self.ctx.foldl_apps(motive, local_indices.iter().copied());
        let motive_app = self.ctx.mk_app(motive_app_base, major);

        let rec_ty = self.ctx.abstr_pi(major, motive_app);
        let rec_ty = self.ctx.abstr_pi_telescope(local_indices, rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(flat_mapped_minors, rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(st.motives.as_slice(), rec_ty);
        let rec_ty = self.ctx.abstr_pi_telescope(st.local_params.as_slice(), rec_ty);

        let recursor = RecursorData {
            info: DeclarInfo {
                name: {
                    let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                    self.ctx.str(ind_name, rec_str_ptr)
                },
                uparams: st.rec_uparams.unwrap(),
                ty: rec_ty,
            },
            all_inductives: Arc::from(st.all_inductives_incl_specialized.iter().map(|x| x.name).collect::<Vec<_>>()),
            num_params: u16::try_from(st.local_params.len()).unwrap(),
            num_indices: u16::try_from(local_indices.len()).unwrap(),
            num_motives: u16::try_from(st.motives.len()).unwrap(),
            num_minors: u16::try_from(flat_mapped_minors.len()).unwrap(),
            rec_rules: Arc::from(rec_rules),
            is_k: st.k_target.unwrap(),
        };

        Declar::Recursor(recursor)
    }

    pub(crate) fn mk_recursors(&mut self, st: &InductiveCheckState<'t>) -> Vec<Declar<'t>> {
        let rec_rules = self.mk_rec_rules(st);
        let mut recursors = Vec::new();
        for (i, ind) in st.all_inductives_incl_specialized.iter().enumerate() {
            let motive = st.motives[i];
            let major = st.majors[i];
            let local_indices = st.local_indices.get(i).unwrap();
            let minors = st.minors.iter().flat_map(|v| v.iter().copied()).collect::<Vec<ExprPtr>>();
            let recursor = self.mk_recursor_aux(
                st,
                ind.name,
                motive,
                major,
                local_indices,
                minors.as_slice(),
                rec_rules[i].as_slice(),
            );
            recursors.push(recursor);
        }
        recursors
    }

    /// Return an ordered map, mapping the specialized recursor names to the
    /// unspecialized recursor names. For example:
    ///
    /// ```ignore
    /// specialized_rec_name_to_unspecialized_rec_name := [
    ///     _nested.Array_1.rec                  |-> Lean.Elab.Term.Do.Code.rec_1
    ///     _nested.List_2.rec                   |-> Lean.Elab.Term.Do.Code.rec_2
    ///     _nested.Lean.Elab.Term.Do.Alt_3.rec  |-> Lean.Elab.Term.Do.Code.rec_3
    /// ]
    /// ```
    fn mk_specialized_rec_to_unspecialized_map(
        &mut self,
        base_mutuals: &[IndTyHeader<'t>],
    ) -> FxIndexMap<NamePtr<'t>, NamePtr<'t>> {
        // The unmodified name of the "main" type being checked, e.g. `Lean.Syntax`
        let main_ind_ty_name = base_mutuals.get(0).map(|zth| zth.name).unwrap();
        let mut specialized_rec_names_to_unspecialized_rec_names = crate::util::new_fx_index_map();
        let rec_str = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));

        // The MODIFIED version looked up in the new environment. The modification would
        // just be additions to `all_ind_names`, which now contains the `_nested.Array`
        // specialized type names.
        let InductiveData { all_ind_names, .. } = self.env.get_inductive(&main_ind_ty_name).unwrap();
        // The modified inductive with the specialized names added must have more elements
        // than the unmodified type's list of names.
        assert!(all_ind_names.len() > base_mutuals.len());
        // For every NEW NESTED elem (new, because we skip `n_types`, skipping all of the base mutuals.)
        // For each modified e.g. `_nested..` name
        for ind_name in all_ind_names.iter().copied().skip(base_mutuals.len()) {
            let specialized_rec_name = self.ctx.str(ind_name, rec_str);
            let unspecialized_rec_name = self.ctx.str(main_ind_ty_name, rec_str);
            let unspecialized_rec_name = self.ctx.append_index_after(
                unspecialized_rec_name,
                (specialized_rec_names_to_unspecialized_rec_names.len() + 1) as u64,
            );
            specialized_rec_names_to_unspecialized_rec_names.insert(specialized_rec_name, unspecialized_rec_name);
        }
        specialized_rec_names_to_unspecialized_rec_names
    }

    /// From `X.mk`, return the un-specialized version of that type, and the
    /// parent inductive name for the constructor
    ///
    /// This looks up the constructor *in the new environment*, so the parent ind name
    /// might be modified, or it might not be. E.g. you might get `Lean.Syntax`, or
    /// you might get `_nested.Array_1`
    fn get_nested_if_aux_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        c: NamePtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>)> {
        // `inductive_name`
        let ConstructorData { inductive_name, .. } = self.env.get_constructor(&c)?;
        let unspecialized_ty = st.nested_to_unspecialized_ty_nofvars.get(inductive_name).copied()?;
        Some((unspecialized_ty, *inductive_name))
    }

    /// If `c` is `_nested_Array_1.mk`, return just `Array.mk`,
    ///
    /// This is only used in restoring recursor rules, since those hold the constructor name.
    fn restore_ctor_name(&mut self, st: &InductiveCheckState<'t>, ctor_name: NamePtr<'t>) -> NamePtr<'t> {
        // from `_nested_Array_1.mk`, retrieve `(Array Lean.Syntax, _nested.Array_1)`
        let (unspecialized_ty, base_ind_name) = self.get_nested_if_aux_ctor(st, ctor_name).unwrap();
        // Now get just `Const(Array, [])`
        let unspecialized_f = self.ctx.unfold_apps_fun(unspecialized_ty);
        // Get just the name for `Array`
        let (unspecialized_ty_name, ..) = self.ctx.try_const_info(unspecialized_f).unwrap();
        // Replace ctor_name[specialized_name |-> unspecialized_name]
        // e.g. `_nested.Array_1.mk |-> Array.mk`
        self.ctx.replace_pfx(ctor_name, base_ind_name, unspecialized_ty_name)
    }

    fn restore_replace(
        &mut self,
        e: ExprPtr<'t>,
        local_params: &[ExprPtr<'t>],
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        match self.replace_f(e, local_params, st, specialized_rec_names_to_unspecialized_rec_names) {
            Some(out) => out,
            None => match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => e,
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let val =
                        self.restore_replace(val, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    let body =
                        self.restore_replace(body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_let(binder_name, binder_type, val, body)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.restore_replace(
                        structure,
                        local_params,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
                App { fun, arg, .. } => {
                    let fun =
                        self.restore_replace(fun, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    let arg =
                        self.restore_replace(arg, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_app(fun, arg)
                }
            },
        }
    }

    /// Traverse an expression replacing one of three appearances:\
    /// 1. `_nested.Array_N`     |-> `Array T`\
    /// 2. `_nested.Array_N.mk`  |-> `Array.mk`\
    /// 3. `_nested.Array_N.rec` |-> `BaseType.rec_N`\
    ///
    /// Gets a map of the specialized recursors tot he "permanent" recursors:
    ///
    /// (_nested.Array_1.rec, Lean.Syntax.rec_1)\
    /// (_nested.List_2.rec, Lean.Syntax.rec_2)
    fn replace_f(
        &mut self,
        e: ExprPtr<'t>,
        local_params: &[ExprPtr<'t>],
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> Option<ExprPtr<'t>> {
        // If it's a recursor application, update the recursor.
        // e.g.
        // replacing(1) const _nested.Lean.PersistentArrayNode_2.rec with Lean.Elab.InfoTree.rec_2
        // replacing(1) const _nested.List_6.rec with Lean.Elab.InfoTree.rec_6
        if let Const { name, levels, .. } = self.ctx.read_expr(e) {
            // If e was `Const(_nested.Array_1.rec)`, return `Const(Lean.Syntax.rec_1)`
            if let Some(rec_name) = specialized_rec_names_to_unspecialized_rec_names.get(&name) {
                return Some(self.ctx.mk_const(*rec_name, levels))
            }
        }
        let (_, c_name, _, e_args) = self.ctx.unfold_const_apps(e)?;
        // If it's an application of e.g. `_nested_Array1`, update
        // Replace one of the specialized types with the un-specialized version:
        // e.g.
        //
        // replacing(2) const _nested.Lean.PersistentArrayNode_2 with Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree
        // replacing(2) const _nested.List_6 with List.{0} (Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree)
        //
        // aux2nested elem := (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
        // aux2nested elem := (_nested.List_2, (List.[0] Lean.Syntax.[]))
        if let Some(nested) = st.nested_to_unspecialized_ty_nofvars.get(&c_name) {
            debug_assert!(e_args.len() >= st.num_params as usize);
            let inner = self.ctx.inst(*nested, local_params);
            let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
            return Some(outer)
        }
        let (nested_no_inst, aux_i_name) = self.get_nested_if_aux_ctor(st, c_name)?;

        debug_assert!(e_args.len() >= st.num_params as usize);
        let nested_inst = self.ctx.inst(nested_no_inst, local_params);
        let (nested_f, i_args) = self.ctx.unfold_apps(nested_inst);
        // Replace one of the nested constructor applications with a regular ctor application.
        //
        // replacing(3) c := _nested.Array_3.mk, auxI_name := _nested.Array_3, I_c := Array, c' := Array.mk.{0}
        // replacing(3) c := _nested.List_4.nil, auxI_name := _nested.List_4, I_c := List, c' := List.nil.{0}
        match self.ctx.read_expr(nested_f) {
            Const { name: i_name, levels, .. } => {
                let cprime_name = self.ctx.replace_pfx(c_name, aux_i_name, i_name);
                let cprime = self.ctx.mk_const(cprime_name, levels);
                let inner = self.ctx.foldl_apps(cprime, i_args.iter().copied());
                let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
                Some(outer)
            }
            _ => panic!("Should be const"),
        }
    }

    /// Restore a single expression (can be a type or value)
    fn restore_e(
        &mut self,
        st: &InductiveCheckState<'t>,
        mut e: ExprPtr<'t>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        let is_pi = matches!(self.ctx.read_expr(e), Pi { .. });
        let mut locals = Vec::new();
        for _ in 0..st.local_params.len() {
            match self.ctx.read_expr(e) {
                // Also match on Lambda for restoring recursor rules.
                Pi { binder_name, binder_style, binder_type, body, .. }
                | Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let local = self.ctx.mk_unique(binder_name, binder_style, binder_type);
                    e = self.ctx.inst(body, &[local]);
                    locals.push(local);
                }
                _ => panic!(),
            }
        }
        let e = self.restore_replace(e, locals.as_slice(), st, nested_rec_name_to_rec_name);
        let out = if is_pi {
            self.ctx.abstr_pi_telescope(locals.as_slice(), e)
        } else {
            self.ctx.abstr_lambda_telescope(locals.as_slice(), e)
        };
        out
    }

    fn restore_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        all_ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        // This map holds the specialized nested elements' recursor names;
        // e.g. `_nested.Array_1.rec |-> Lean.Syntax.rec_1`,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        // `rec_name` This can be either an old/base inductive rec name, or a fresh/specialized name
        // Either `Syntax.rec`, or `_nested.Array_N.rec`
        rec_name: NamePtr<'t>,
    ) -> RecursorData<'t> {
        // resolve e.g. `_nested.Array_1.rec` to `Lean.Syntax.rec_1`
        let resolved_rec_name =
            specialized_rec_names_to_unspecialized_rec_names.get(&rec_name).copied().unwrap_or(rec_name);
        // The new environment's recursor for this type; e.g. the recursor
        // that's in the environment for _nested.Array_1.rec
        let new_env_rec @ RecursorData { .. } = self.env.get_recursor(&rec_name).cloned().unwrap();
        let restored_ty = self.restore_e(st, new_env_rec.info.ty, specialized_rec_names_to_unspecialized_rec_names);
        let mut rules = Vec::new();
        for rule in new_env_rec.rec_rules.iter().copied() {
            let val = self.restore_e(st, rule.val, specialized_rec_names_to_unspecialized_rec_names);
            let ctor_name =
                if rec_name == resolved_rec_name { rule.ctor_name } else { self.restore_ctor_name(st, rule.ctor_name) };
            rules.push(RecRule { ctor_name, val, ..rule })
        }
        RecursorData {
            info: DeclarInfo { name: resolved_rec_name, ty: restored_ty, ..new_env_rec.info },
            all_inductives: all_ind_names_no_specialized.clone(),
            rec_rules: Arc::from(rules),
            ..new_env_rec
        }
    }

    fn check_restored_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        rec_name: NamePtr<'t>,
    ) {
        let restored = self.restore_recursor1(st, ind_names_no_specialized, nested_rec_name_to_rec_name, rec_name);
        let resolved_rec_name = nested_rec_name_to_rec_name.get(&rec_name).copied().unwrap_or(rec_name);
        match self.env.get_old_declar(&resolved_rec_name) {
            Some(Declar::Recursor(original @ RecursorData { .. })) => {
                self.tc_cache.clear();
                self.assert_def_eq(original.info.ty, restored.info.ty);
                // have to do the rec rules as well.
                assert_eq!(original.rec_rules.len(), restored.rec_rules.len());
                for i in 0..original.rec_rules.len() {
                    let old = original.rec_rules[i];
                    let new = restored.rec_rules[i];
                    assert_eq!(old.ctor_name, new.ctor_name);
                    self.tc_cache.clear();
                    self.assert_def_eq(old.val, new.val);
                }
            }
            _ => {}
        }
    }

    fn restore_recursors(
        &mut self,
        st: &InductiveCheckState<'t>,
        specialized_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
    ) {
        // Check the recursors for the base inductives (NOT the specialized types)
        for old_ind_name in ind_names_no_specialized.iter().copied() {
            let rec_name = {
                let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                self.ctx.str(old_ind_name, rec_str_ptr)
            };
            self.check_restored_recursor1(st, ind_names_no_specialized, specialized_rec_name_to_rec_name, rec_name)
        }

        // Check the recursors constructed for the specialized types,
        // like `_nested.Array_1.rec` after restoring it to `Lean.Syntax.rec_1`
        for specialized_ty_rec_name in specialized_rec_name_to_rec_name.keys().copied() {
            self.check_restored_recursor1(
                st,
                ind_names_no_specialized,
                specialized_rec_name_to_rec_name,
                specialized_ty_rec_name,
            )
        }
    }

    fn check_restored_ctor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_name_map: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        old_ctor: &ConstructorData<'t>,
    ) {
        let new_ctor @ ConstructorData { .. } = self.env.get_constructor(&old_ctor.info.name).unwrap();
        let new_ty = self.restore_e(st, new_ctor.info.ty, rec_name_map);
        self.tc_cache.clear();
        self.assert_def_eq(old_ctor.info.ty, new_ty);
    }

    fn restore_and_check(
        &mut self,
        st: &InductiveCheckState<'t>,
        unmodified_mutuals: &Vec<IndTyHeader<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
    ) {
        let specialized_to_unspecialized_rec_names = self.mk_specialized_rec_to_unspecialized_map(unmodified_mutuals);
        for unmodified_ind_type in unmodified_mutuals.iter() {
            match (
                self.env.get_old_declar(&unmodified_ind_type.name),
                self.env.get_temp_declar(&unmodified_ind_type.name),
            ) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }

            for ctor in unmodified_ind_type.ctors.iter() {
                let ctor = match self.env.get_old_declar(&ctor.name) {
                    Some(Declar::Constructor(c)) => c.clone(),
                    _ => panic!(),
                };
                self.check_restored_ctor1(st, &specialized_to_unspecialized_rec_names, &ctor);
            }
        }
        self.restore_recursors(st, &specialized_to_unspecialized_rec_names, ind_names_no_specialized);
    }
}
