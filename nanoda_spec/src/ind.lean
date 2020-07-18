import 
    .utils
    .name
    .level
    .expr
    .env
    .tc


open Name Level Expr Declar InferFlag


/-
Indblock is all of the information we get from the export file
about our Inductive type, plus params. Having this saves us from 
a lot of repetition in the spec, so we're going to consider this
a proper item that will be printed as an 7 '.' separated items
which should be treated as a 7-tuple (they'll be in this order)
-/
structure Indblock :=
(is_unsafe : bool)
(num_params : nat)
(uparams : list Level)
(ind_names : list Name)
(ind_types : list Expr)
(ctor_names : list Name)
(ctor_types : list Expr)

/-
printed as a list of all 13 items. 
Should be treated as a tuple.
Should be output in order shown.
-/
structure CheckedIndblock extends Indblock :=
(codom_level : Level)
(is_zero : bool)
(is_nonzero : bool)
(params : list Expr)
(indices : list Expr)
(ind_consts : list Expr)

inductive mkLocalParams :
    ∀ (ind_type_cursor : Expr)
      (num_params : nat)
      (params : list Expr),
      Prop
| base (ind_type_cursor : Expr) : 
    let num_params := 0,
        params : list Expr := []
    in mkLocalParams ind_type_cursor num_params params

| step
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (num_params : nat)
    (serial : nat)
    (b' : Expr)
    (params_tl : list Expr) :
    let ind_type_cursor := (mkPi n t s b),
        num_params' := nat.pred num_params,
        params_hd := mkLocal n t s serial,          
        params := (params_hd :: params_tl)
    in
    inst1 b params_hd b'
    -> mkLocalParams b' num_params' params_tl
    -> mkLocalParams ind_type_cursor num_params params


/-
A note abut the StepParam constructor:
The requirement in the C++ kernel is that the types of the parameters
for all inductives in a mutual block are definitionally equal; it doesn't
require structural/pointer equality. While it seems highly unlikely that 
Lean would produce an export file with mutuals that have parameters
which are ONLY definitionally equal, it is technically a possibility.
-/
inductive handleTelescope1 
    (indblock : Indblock)
    (ind_name : Name) 
    (codom_level : Level) :
    ∀ (ind_type_cursor : Expr)
      (rem_params : list Expr)
      -- vv indices, codom_level, ind_const
      (result : (list Expr × Level × Expr)),
      Prop
| base (ind_type_cursor : Expr) : 
    let rem_params : list Expr := [],
        ind_const := mkConst ind_name indblock.uparams,
        result : (list Expr × Level × Expr) := ([], codom_level, ind_const)
    in
    isPi ind_type_cursor ff
    -> ensureSort ind_type_cursor codom_level
    -> handleTelescope1 ind_type_cursor rem_params result

| stepIndex
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (indices_tl : list Expr)
    (b' : Expr) :
    let ind_type_cursor := (mkPi n t s b),
        rem_params : list Expr := [],
        indices_hd := mkLocal n t s serial,
        ind_const := mkConst ind_name indblock.uparams,
        rec_result := (indices_tl, codom_level, ind_const),
        result := ((indices_hd :: indices_tl), codom_level, ind_const)
    in 
    inst1 b indices_hd b'
    -> handleTelescope1 b' rem_params rec_result
    -> handleTelescope1 ind_type_cursor rem_params result

| stepParam
    (n : Name)
    (t1 : Expr)
    (t2 : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (params_tl : list Expr)
    (b' : Expr)
    (result : (list Expr × Level × Expr)) :
    let ind_type_cursor := mkPi n t2 s b,
        params_hd := mkLocal n t1 s serial,
        rem_params := (params_hd :: params_tl)
    in
    defEq t1 t2 
    -> inst1 b params_hd b'
    -> handleTelescope1 b' params_tl result
    -> handleTelescope1 ind_type_cursor rem_params result

inductive handleTelescopes 
    (indblock : Indblock)
    (params : list Expr)
    (codom_level : Level) :
    ∀ (rem_ind_names : list Name)
      (rem_ind_types : list Expr)
      (result : (list Expr × Level × list Expr)),
      Prop
| base 
    (i_ns_hd : Name)
    (i_ts_hd : Expr)
    (indices : list Expr) :
    let ind_const := mkConst i_ns_hd indblock.uparams,
        rec_result := (indices, codom_level, ind_const),
        rem_ind_names := [i_ns_hd],
        rem_ind_types := [i_ts_hd],
        result := (indices, codom_level, [ind_const])
    in
    handleTelescope1 indblock i_ns_hd codom_level i_ts_hd params rec_result
    -> handleTelescopes rem_ind_names rem_ind_types result

| step
  (i_ns_hd : Name)
  (i_ns_tl : list Name)
  (i_ts_hd : Expr)
  (i_ts_tl : list Expr)
  (indices_r : list Expr)
  (indices_l : list Expr)
  (codom_level2 : Level)
  (ind_cs_tl : list Expr) :
  let ind_cs_hd := mkConst i_ns_hd  indblock.uparams,
      ind_cs := (mkConst i_ns_hd indblock.uparams) :: ind_cs_tl,
      rec_result := (indices_r, codom_level, ind_cs_tl),       
      hd_result := (indices_l, codom_level2, ind_cs_hd),
      indices := indices_l ++ indices_r,
      rem_ind_names := (i_ns_hd :: i_ns_tl),
      rem_ind_types := (i_ts_hd :: i_ts_tl),
      result := (indices, codom_level, ind_cs)
  in
  handleTelescopes i_ns_tl i_ts_tl rec_result
  -> handleTelescope1 indblock i_ns_hd codom_level i_ts_hd params hd_result
  -> eqAntisymm codom_level codom_level2 tt
  -> handleTelescopes rem_ind_names rem_ind_types result


/-
the listGet hypothesis won't be logged.
`ind_names` and `ind_types` are present twice in the handleTelescopes hypothesis
to show that `handleTelescopes` has been constructed for lists that are 
equal to the lists in the Indblock
-/
inductive checkIndTypes 
    (indblock : Indblock)
    (params : list Expr)
    (indices : list Expr)
    (codom_level : Level)
    (ind_consts : list Expr)
    : Prop
| base :
    let telescopes_result := (indices, codom_level, ind_consts),
        ind_types_hd := getInfal indblock.ind_types 0
    in 
    -- vv the listGet hypothesis won't be logged; just an assertion
    -- that the 'model' type we get the block parameters from 
    -- is the 0th element of the block ind types list
    --listGet indblock.ind_types 0 (some ind_types_hd)
    mkLocalParams ind_types_hd indblock.num_params params
    -> handleTelescopes 
            indblock
            params
            codom_level
            indblock.ind_names
            indblock.ind_types
            telescopes_result
    -> checkIndTypes 


inductive mkIndTypes (indblock : Indblock) :
    ∀ (ind_names : list Name)
      (ind_types : list Expr)
      (ctor_names : list Name)
      (declars : list Declar),
      Prop
| base (env : Env) : 
    let ind_names : list Name := [],
        ind_types : list Expr := [],
        ctor_names : list Name := [],
        declars : list Declar := []
    in 
    mkIndTypes ind_names ind_types ctor_names declars

| step
    (i_ns_hd : Name)
    (i_ns_tl : list Name)
    (i_ts_hd : Expr)
    (i_ts_tl : list Expr)
    (c_ns_curr : list Name)
    (c_ns_rest : list Name)
    (ds_tl : list Declar) :
    let ind_names := (i_ns_hd :: i_ns_tl),
        ind_types := (i_ts_hd :: i_ts_tl),
        ctor_names := (c_ns_curr ++ c_ns_rest),
        ds_hd := Inductive i_ns_hd indblock.uparams i_ts_hd indblock.num_params indblock.ind_names c_ns_curr indblock.is_unsafe,
        ds := (ds_hd :: ds_tl)
    in
    mkIndTypes i_ns_tl i_ts_tl c_ns_rest ds_tl
    -> mkIndTypes ind_names ind_types ctor_names ds





    
-- The bool here will always be `tt` 
inductive validParamApps : ∀ (rem_ind_apps rem_block_params : list Expr), bool -> Prop
| base (rem_ind_apps : list Expr) : 
    let rem_block_params : list Expr := [],
        b := tt
    in validParamApps rem_ind_apps rem_block_params b

| step 
    (hd : Expr)
    (ind_apps_tl : list Expr)
    (block_params_tl : list Expr) : 
    let rem_ind_apps := (hd :: ind_apps_tl),
        rem_block_params := (hd :: block_params_tl),
        b := tt
    in
    validParamApps ind_apps_tl block_params_tl b
    -> validParamApps rem_ind_apps rem_block_params b


/-
The constructor has to have a number of arguments applied to it that
is equal to the number of params and indices on the inductive type,
and the parameters have to be equal to the block parameters.

This can be false; is used as a test in isRecArgument

-/
inductive isValidIndApp 
    (indblock : CheckedIndblock) 
    (ind_type : Expr)
    (ind_const : Expr)
    (stripped_ctor_type : Expr) :
    ∀ (b : bool),
      Prop

| baseFf
    (unfolded_fun : Expr)
    (ind_apps : list Expr)
    (apps_len : nat)
    (telescope_size : nat) :
    -- ASSERT : ind_apps.length = apps_len
    let b1 : bool := ind_const = unfolded_fun,
        b2 : bool := apps_len = telescope_size,
        b : bool := b1 && b2
    in
    unfoldApps stripped_ctor_type (ind_const, ind_apps)
    -> telescopeSize ind_type telescope_size
    -> isValidIndApp (b1 && b2)
    
| baseTt 
    (unfolded_fun : Expr)
    (ind_apps : list Expr)
    (apps_len : nat)
    (telescope_size : nat)
    (b1 : bool) :
    let b2 : bool := ind_const = unfolded_fun,
        b3 : bool := apps_len = telescope_size,
        b := b1 && b2 && b3
    in
    -- ASSERT : ind_apps.len = apps_len
    unfoldApps stripped_ctor_type (ind_const, ind_apps)
    -> telescopeSize ind_type telescope_size
    -> validParamApps ind_apps indblock.params b1
    -> isValidIndApp b

inductive whichValidIndApp 
    (indblock : CheckedIndblock)
    (u_i_ty : Expr) :
    ∀ (ind_types ind_consts : list Expr) 
      (ind_ty_index : nat),
      Prop
| base 
    (ind_types_hd : Expr) 
    (ind_types_tl : list Expr)
    (ind_consts_hd : Expr)        
    (ind_consts_tl : list Expr) :
    let ind_types := (ind_types_hd :: ind_types_tl),
        ind_consts := (ind_consts_hd :: ind_consts_tl),
        ind_ty_idx := 0
    in
    isValidIndApp indblock ind_types_hd ind_consts_hd u_i_ty tt
    -> whichValidIndApp ind_types ind_consts ind_ty_idx

| step
    (ind_types_hd : Expr) 
    (ind_types_tl : list Expr)
    (ind_consts_hd : Expr)        
    (ind_consts_tl : list Expr)
    (ind_ty_idx' : nat) :
    let ind_types := (ind_types_hd :: ind_types_tl),
        ind_consts := (ind_consts_hd :: ind_consts_tl),
        ind_ty_idx := 1 + ind_ty_idx'
    in
    isValidIndApp indblock ind_types_hd ind_consts_hd u_i_ty ff
    -> whichValidIndApp ind_types_tl ind_consts_tl ind_ty_idx'
    -> whichValidIndApp ind_types ind_consts ind_ty_idx

inductive isRecArgument 
    (indblock : CheckedIndblock)
    (ind_type : Expr)
    (ind_const : Expr) :
    ∀ (ctor_arg : Expr)
      (result : bool),
      Prop

| base 
    (ctor_arg : Expr)
    (ctor_arg' : Expr)
    (result : bool) :
    whnf ctor_arg ctor_arg'
    -> isValidIndApp indblock ind_type ind_const ctor_arg' result
    -> isRecArgument ctor_arg result

| step
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (ctor_arg' : Expr)
    (b' : Expr)
    (result : bool) :
    let ctor_arg := mkPi n t s b,
        local_expr := mkLocal n t s serial
    in
    whnf ctor_arg ctor_arg'
    -> inst1 b local_expr b'
    -> isRecArgument b' result
    ->  isRecArgument ctor_arg result
    
-- assertion-like; should always be true.
-- There's an implicit assertion here that if the block is unsafe
-- then it has to use the `byUnsafe` constructor,
-- and the others are for blocks where is_unsafe is false.
inductive checkPositivity1
    (indblock : CheckedIndblock)
    (ind_type : Expr)
    (ind_const : Expr) :
    ∀ (ctor_type : Expr),
      Prop

-- indblock.is_unsafe = tt -> ..
| byUnsafe (ctor_type : Expr) : checkPositivity1 ctor_type

-- indblock.is_unsafe = ff
| noIndOccs
    (ctor_type : Expr)
    (ctor_type' : Expr) :
    whnf ctor_type ctor_type'
    -> hasIndOcc ctor_type' indblock.ind_names ff
    -> checkPositivity1 ctor_type

-- indblock.is_unsafe = ff
| baseValid
    (ctor_type : Expr)
    (ctor_type' : Expr) :
    whnf ctor_type ctor_type'
    -> isValidIndApp indblock ind_type ind_const ctor_type' tt
    -> checkPositivity1 ctor_type
  
-- indblock.is_unsafe = ff
| stepHasInd
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (ctor_type : Expr)
    (b' : Expr) :
    let ctor_type' := mkPi n t s b,
        local_expr := mkLocal n t s serial
    in
    whnf ctor_type ctor_type'
    -> hasIndOcc t indblock.ind_names ff
    -> inst1 b local_expr b'
    -> checkPositivity1 b'
    -> checkPositivity1 ctor_type


inductive checkCtor1
    (indblock : CheckedIndblock)
    (ind_type : Expr)
    (ind_const : Expr) :
    ∀ (rem_params : list Expr)
      (ctor_type : Expr),
      Prop

| base (ctor_type : Expr) :
    let rem_params : list Expr := []
    in
    isValidIndApp indblock ind_type ind_const ctor_type tt
    -> checkCtor1 rem_params ctor_type

-- You can combine this and stepLe
-- if you have a disjunction (isZero l tt ∨ leq l codom_level tt)
| stepProp
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (sort_level : Level)
    (serial : nat)
    (b' : Expr) : 
    let rem_params : list Expr := [],
        ctor_type := mkPi n t s b,
        local_expr := mkLocal n t s serial
    in
    ensureType t sort_level
    -> isZero sort_level tt
    -> checkPositivity1 indblock ind_type ind_const t
    -> inst1 b local_expr b'
    -> checkCtor1 rem_params b'
    -> checkCtor1 rem_params ctor_type

| stepLe
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (sort_level : Level)
    (serial : nat)
    (b' : Expr) : 
    let rem_params : list Expr := [],
        ctor_type := mkPi n t s b,
        local_expr := mkLocal n t s serial
    in
    ensureType t sort_level
    -> leq sort_level indblock.codom_level tt
    -> checkPositivity1 indblock ind_type ind_const t
    -> inst1 b local_expr b'
    -> checkCtor1 rem_params b'
    -> checkCtor1 rem_params ctor_type

| stepParam
    (p_n : Name)
    (p_t : Expr)
    (p_s : Bstyle)
    (serial : nat)
    (params_tl : list Expr)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (b' : Expr) :
    let ps_hd := mkLocal p_n p_t p_s serial,
        ps := (ps_hd :: params_tl),
        ctor_type := mkPi n t s b
    in
    defEq t p_t
    -> inst1 b ps_hd b'
    -> checkCtor1 params_tl b'
    -> checkCtor1 ps ctor_type


/-
where a `group` means the list of constructors for one inductive
type in a block, as opposed to all of the constructors in a block, which may 
be spread across a number of mutually inductive types.
-/
inductive mkCtorGroup
    (indblock : CheckedIndblock)
    (ind_name : Name)
    (ind_type : Expr)
    (ind_const : Expr) :
    ∀ (rem_ctor_names : list Name)
      (rem_ctor_types : list Expr)
      (ds : list Declar),
      Prop
| base : 
    let rem_ctor_names : list Name := [],
        rem_ctor_types : list Expr := [],
        ds : list Declar := []
    in mkCtorGroup rem_ctor_names rem_ctor_types ds

| step 
    (ns_hd : Name)
    (ns_tl : list Name)
    (ts_hd : Expr)
    (ts_tl : list Expr)
    (telescope_size : nat)
    (ds_tl : list Declar) :
    let num_fields := telescope_size - indblock.num_params,
        d := Constructor ns_hd indblock.uparams ts_hd ind_name num_fields indblock.num_params indblock.is_unsafe,
        rem_ctor_names := ns_hd :: ns_tl,
        rem_ctor_types := ts_hd :: ts_tl,
        ds := (d :: ds_tl)
    in
    mkCtorGroup ns_tl ts_tl ds_tl
    -> telescopeSize ts_hd telescope_size
    -> checkCtor1 indblock ind_type ind_const indblock.params ts_hd
    -> mkCtorGroup rem_ctor_names rem_ctor_types ds


/-
Has two constructors since technically we're supposed to
declare these in blocks
-/
inductive mkCtors (indblock : CheckedIndblock) :
    ∀ (rem_ind_names : list Name)
      (rem_ind_types : list Expr)
      (rem_ind_consts : list Expr)
      (rem_c_names : list Name)
      (rem_c_types : list Expr)
      (ds : list Declar),
      Prop

| base : 
    let rem_ind_names : list Name := [],
        rem_ind_types : list Expr := [],
        rem_ind_consts : list Expr := [],
        rem_c_names : list Name := [],
        rem_c_types : list Expr := [],
        ds : list Declar := []
    in
    mkCtors [] [] [] [] [] []

| step
    (ind_n_hd : Name)
    (ind_n_tl : list Name)
    (ind_t_hd : Expr)
    (ind_t_tl : list Expr)
    (ind_c_hd : Expr)
    (ind_c_tl : list Expr)
    (curr_c_ns : list Name)
    (rest_c_ns : list Name)
    (curr_c_ts : list Expr)
    (rest_c_ts : list Expr)
    (curr_ds : list Declar)
    (rest_ds : list Declar) :
    let rem_ind_names := (ind_n_hd :: ind_n_tl),
        rem_ind_types := (ind_t_hd :: ind_t_tl),
        rem_ind_consts := (ind_c_hd :: ind_c_tl),
        rem_c_names := (curr_c_ns ++ rest_c_ns),
        rem_c_types := (curr_c_ts ++ rest_c_ts),
        ds :=  (curr_ds ++ rest_ds)
    in
    mkCtors ind_n_tl ind_t_tl ind_c_tl rest_c_ns rest_c_ts rest_ds
    -> mkCtorGroup indblock ind_n_hd ind_t_hd ind_c_hd curr_c_ns curr_c_ts curr_ds
    -> mkCtors rem_ind_names rem_ind_types rem_ind_consts rem_c_names rem_c_types ds
        



/-
1. Collect the list of constructor arguments that are NOT in sort 0/Prop.
2. Collect the list of arguments being passed to the inductive 
   at the end of the construction.

3. If list 1 is NOT a subset of list 2, it means the constructor is taking
   arguments that are neither params nor indices, and are not propositions,
   meaning the type in question cannot be large eliminating.
-/
inductive largeElimTestAux :
    ∀ (params_rem : nat)
      (ctor_type : Expr)
      (nonzero_ctor_args : list Expr)
      (large_eliminating : bool),
      Prop

| base 
    (ctor_type : Expr)
    (ctor_f : Expr)
    (ctor_args : list Expr)
    (nonzero_ctor_args : list Expr)
    (large_eliminating : bool) :
    let params_rem := 0
    in
    isPi ctor_type ff
    -> unfoldApps ctor_type (ctor_f, ctor_args)
    -> listSubset nonzero_ctor_args ctor_args large_eliminating
    -> largeElimTestAux params_rem ctor_type nonzero_ctor_args large_eliminating

| stepCtorArgZero
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (t_level : Level)
    (serial : nat)
    (b' : Expr)
    (nonzero_ctor_args : list Expr)
    (large_eliminating : bool) :
    let params_rem := 0,
        ctor_type := mkPi n t s b,
        local_expr := mkLocal n t s serial
    in
    ensureType t t_level
    -> isZero t_level tt
    -> inst1 b local_expr b'
    -> largeElimTestAux params_rem b' nonzero_ctor_args large_eliminating
    -> largeElimTestAux params_rem ctor_type nonzero_ctor_args large_eliminating

| StepCtorArgNonzero
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (t_level : Level)
    (serial : nat)
    (b' : Expr)
    (nonzero_ctor_args_tl : list Expr)
    (large_eliminating : bool) :
    let params_rem := 0,
        ctor_type := mkPi n t s b,
        local_expr := mkLocal n t s serial,
        nonzero_ctor_args := (local_expr :: nonzero_ctor_args_tl)
    in
    ensureType t t_level
    -> isZero t_level ff
    -> inst1 b local_expr b'
    -> largeElimTestAux params_rem b' nonzero_ctor_args large_eliminating
    -> largeElimTestAux params_rem ctor_type nonzero_ctor_args_tl large_eliminating

| stepParam
    (params_rem : nat)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b' : Expr)
    (large_eliminating : bool) :
    let params_rem' := params_rem - 1,
        ctor_type := mkPi n t s b,
        local_expr := mkLocal n t s serial,
        nonzero_ctor_args : list Expr := []
    in
    inst1 b local_expr b'
    -> largeElimTestAux params_rem' b' nonzero_ctor_args large_eliminating 
    -> largeElimTestAux params_rem ctor_type nonzero_ctor_args large_eliminating


-- ind_types, ctor_type
inductive largeElimTest (indblock : CheckedIndblock) : ∀ (large_eliminating : bool), Prop

| nonZero :
    let large_eliminating := tt
    in 
    isNonzero indblock.codom_level large_eliminating 
    -> largeElimTest large_eliminating

| isMutual :
    let large_eliminating := ff
    in
    -- ASSERT : indblock.ind_types.length > 1
    isNonzero indblock.codom_level large_eliminating
    -> largeElimTest large_eliminating

| manyCtors :  
    let large_eliminating := ff
    in
    -- ASSERT : indblock.ctor_types.length > 1
    isNonzero indblock.codom_level large_eliminating
    -> largeElimTest large_eliminating

| noCtors : 
    let ctor_types : list Expr := [],
        large_eliminating := tt
    in
    largeElimTest large_eliminating

| byAux (ctor_type : Expr) (large_eliminating : bool) :  
    let nonzero_ctor_args : list Expr := []
    in
    -- ASSERT : indblock.ctor_types == [ctor_type]
    -- ASSERT : indblock.ind_types.length ≤ 1
    isNonzero indblock.codom_level ff
    -> largeElimTestAux indblock.num_params ctor_type nonzero_ctor_args large_eliminating
    -> largeElimTest large_eliminating


/-
the uniqueness constraint on the parameter is just that it's
not in the list of universe parameters for the inductive.
-/
inductive mkElimLevel (indblock : CheckedIndblock) : ∀ (elim_level : Level), Prop
| largeEliminating (elim_level : Level) :  
    largeElimTest indblock tt
    -> elim_level ∉ indblock.uparams 
    -> mkElimLevel elim_level

| smallEliminating : 
    largeElimTest indblock ff
    -> mkElimLevel Zero

inductive initKTargetAux :
  ∀ (params_rem : nat)
    (ctor_type : Expr)
    (k_target : bool),
    Prop

| base (ctor_type : Expr) (is_pi : bool) :
    let params_rem := 0,
        k_target := bnot is_pi
    in
    isPi ctor_type is_pi
    -> initKTargetAux params_rem ctor_type k_target

| stepParam 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (params_rem : nat)
    (k_target : bool) :
    let ctor_type := mkPi n t s b,
        params_rem' := params_rem - 1
    in
    initKTargetAux params_rem' b k_target
    -> initKTargetAux params_rem ctor_type k_target

inductive initKTarget (indblock : CheckedIndblock) : ∀ (k_target : bool), Prop
| isMutual : 
    let k_target := ff
    in
    -- ASSERT : indblock.ind_types.length > 1
    initKTarget k_target
| nonzero : 
    let k_target := ff
    in
    isZero indblock.codom_level k_target
    -> initKTarget k_target

| notOneCtor (ctor_types : list Expr) : 
    let k_target := ff 
    in
    -- ASSERT : ctor_types.length ≠ 1
    initKTarget k_target

| byAux (ctor_type : Expr) (k_target : bool) : 
    -- assert : indblock.ctor_types = ctor_types
    initKTargetAux indblock.num_params ctor_type k_target
    -> initKTarget k_target


/-
In the implementation, the size of each `indices_l` list
is determined by the type `t` being worked on, it's calculated
as the num_params - telescopeSize(t), but in light of the last
conversation about mm0 and the tedious take/skip stuff on lists,
I'll leave that to the implementation of the verifier.
-/
inductive mkMajorsAux
    (indblock : CheckedIndblock)
    : ∀ (indices : list Expr)
        (ind_consts : list Expr)
        (majors : list Expr),
        Prop

| base : 
    let indices : list Expr := [],
        ind_consts : list Expr := [],
        majors : list Expr := []
    in mkMajorsAux indices ind_consts majors

| step 
    (indices_l : list Expr)
    (indices_r : list Expr)
    (ind_consts_hd : Expr)
    (ind_consts_tl : list Expr)
    (majors_tl : list Expr)
    (major_typeA : Expr)
    (major_typeB : Expr)
    (serial : nat)
    :
    let indices := indices_l ++ indices_r,
        ind_consts := ind_consts_hd :: ind_consts_tl,
        major_name := Str Anon "t",
        major_bstyle := Bstyle.Default,
        majors_hd := mkLocal major_name major_typeB major_bstyle serial,
        majors := majors_hd :: majors_tl

    in
    mkMajorsAux indices_r ind_consts_tl majors_tl
    -> foldlApps ind_consts_hd indblock.params major_typeA
    ->  foldlApps major_typeA indices_l major_typeB
    -> mkMajorsAux indices ind_consts majors

-- This will be output just as MkMajorsAux with the 
-- corresponding arguments
def mkMajors 
    (indblock : CheckedIndblock)
    (params : list Expr)
    (indices : list Expr)
    (ind_consts : list Expr)
    (majors : list Expr)
    := mkMajorsAux indblock indices ind_consts majors

/-
This will be one of the few things that's a hard change
from lean3 to lean4; all motives are dependent in lean4,
but lean3 export files produce terms that depend on the existence
of an independent recursor, so we need to keep it in.

Also the CPP version doesn't add the integer suffix to the name
if it's not a mutual inductive, but it doesn't really make
a difference. If it ends up being distracting in the pretty printed
output I'll change it.
-/
inductive mkMotive 
    (elim_level : Level)
    (indices : list Expr)
    (ind_type_idx : nat)
    (major : Expr) :
    ∀ (motive : Expr),
      Prop

| mkIndep 
    (serial : nat) 
    (motive_type : Expr) :
    let elim_sort : Expr := mkSort elim_level,
        motive_name  := Num (Str Anon "C") ind_type_idx,
        motive_bstyle := Bstyle.Implicit,
        motive := mkLocal motive_name motive_type motive_bstyle serial
    in
    foldPis indices elim_sort motive_type
    -> mkMotive motive

| mkDep
    (serial : nat)
    (motive_typeA : Expr)
    (motive_typeB : Expr) :
     let elim_sort : Expr := mkSort elim_level,
        motive_name  := Num (Str Anon "C") ind_type_idx,
        motive_bstyle := Bstyle.Implicit,
        motive := mkLocal motive_name motive_typeB motive_bstyle serial
    in
    applyPi major elim_sort motive_typeA
    -> foldPis indices motive_typeA motive_typeB
    -> mkMotive motive   

-- make all motives for the block
/-
Here again, the length of each `indices_l` chunk is the number
of indices for the inductive type (num_params - telescopeSize)
-/
inductive mkMotivesAux (elim_level : Level) :
    ∀ (ind_type_idx : nat)
      (majors : list Expr)
      (indices : list Expr)
      (motives : list Expr),
      Prop

| base (ind_type_idx : nat) :
    let majors : list Expr := [],
        indices : list Expr := [],
        motives : list Expr := []
    in mkMotivesAux ind_type_idx majors indices motives

| step
    (ind_type_idx : nat)
    (majors_hd : Expr)
    (majors_tl : list Expr)
    (indices_l : list Expr)
    (indices_r : list Expr)
    (motives_hd : Expr)
    (motives_tl : list Expr) :
    let ind_type_idx' := 1 + ind_type_idx,
        majors := majors_hd :: majors_tl,
        indices := indices_l ++ indices_r,
        motives := motives_hd :: motives_tl
    in
    mkMotivesAux ind_type_idx' majors_tl indices_r motives_tl
    -> mkMotive elim_level indices_l ind_type_idx majors_hd motives_hd
    -> mkMotivesAux ind_type_idx majors indices motives

-- will show up as mkMotivesAux
def mkMotives
    (elim_level : Level)
    (majors : list Expr)
    (indices : list Expr)
    (motives : list Expr)
    := mkMotivesAux elim_level 0 majors indices motives

    
-- seprates constructor args into nonrecursive and recrusive,
-- also returns the instantiated inner expression.
inductive sepCtorArgs
    (indblock : CheckedIndblock)
    (ind_type : Expr)
    (ind_const : Expr) :
    ∀ (rem_params : list Expr)
      (ctor_type : Expr)
      (all_args : list Expr)
      (rec_args : list Expr)
      (inner_type : Expr),
      Prop
        
| base (ctor_type : Expr) :
    let rem_params : list Expr := [],
        all_args : list Expr := [],
        rec_args : list Expr := [],
        inner_type := ctor_type
    in
    sepCtorArgs rem_params ctor_type all_args rec_args inner_type

| stepNonrecArg 
    (inner_type : Expr)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b' : Expr)
    (all_args_tl : list Expr)
    (rec_args : list Expr) :
    let rem_params : list Expr := [],
        ctor_type := mkPi n t s b,
        arg := mkLocal n t s serial,
        all_args := arg :: all_args_tl
    in
    inst1 b arg b'
    -> sepCtorArgs rem_params b' all_args_tl rec_args inner_type
    -> isRecArgument indblock ind_type ind_const t ff
    -> sepCtorArgs rem_params ctor_type all_args rec_args inner_type

| stepRecArg 
    (inner_type : Expr)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b' : Expr)
    (all_args_tl : list Expr)
    (rec_args_tl : list Expr) :
    let rem_params : list Expr := [],
        ctor_type := mkPi n t s b,
        arg := mkLocal n t s serial,
        all_args := arg :: all_args_tl,
        rec_args := arg :: rec_args_tl
    in
    inst1 b arg b'
    -> sepCtorArgs rem_params b' all_args_tl rec_args_tl inner_type
    -> isRecArgument indblock ind_type ind_const t tt
    -> sepCtorArgs rem_params ctor_type all_args rec_args inner_type

| stepParam
    (inner_type : Expr)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (b' : Expr)
    (all_args : list Expr)
    (rec_args : list Expr)
    (rem_params_hd : Expr)
    (rem_params_tl : list Expr) :
    let rem_params := rem_params_hd :: rem_params_tl,
        ctor_type := mkPi n t s b
    in
    inst1 b rem_params_hd b'
    -> sepCtorArgs rem_params_tl b' all_args rec_args inner_type
    -> sepCtorArgs rem_params ctor_type all_args rec_args inner_type

inductive getIIndices
    (indblock : CheckedIndblock)
    (type_cursor : Expr)
    (valid_app_idx : nat) :
    ∀ (indices : list Expr),
      Prop
| base (type_fun : Expr) (type_args : list Expr) :
    let indices := type_args.drop (indblock.params.length)
    in
     whichValidIndApp indblock type_cursor indblock.ind_types indblock.ind_consts valid_app_idx
     -> unfoldApps type_cursor (type_fun, type_args)
     -> getIIndices indices

inductive handleRecArgsAux :
    ∀ (type_cursor : Expr)
      (inner : Expr)
      (args : list Expr),
      Prop

| base (type_cursor : Expr) :
    let inner := type_cursor,
        args : list Expr := []
    in
    isPi type_cursor ff
    -> handleRecArgsAux type_cursor inner args

| step
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b_prime : Expr)
    (b_prime_red : Expr)
    (inner : Expr)
    (args_tl : list Expr) :
    let type_cursor := mkPi n t s b,
        local_expr := mkLocal n t s serial,
        args := local_expr :: args_tl
    in
    inst1 b local_expr b_prime
    -> whnf b_prime b_prime_red
    -> handleRecArgsAux b_prime_red inner args_tl
    -> handleRecArgsAux type_cursor inner args

/-
Another place where there's a distinction between
indep/dep eliminators.
-/
inductive handleRecArgsMinor (indblock : CheckedIndblock) (motives : list Expr) :
  ∀ (rem_rec_args : list Expr)
    (self_idx : nat)
    (result  : list Expr),
    Prop
| base (self_idx : nat) :
    let rem_rec_args : list Expr := [],
        result : list Expr := []
    in handleRecArgsMinor rem_rec_args self_idx result

| stepIndep
    (self_idx : nat)
    (rec_args_hd : Expr)
    (rec_args_tl : list Expr)
    (result_tl : list Expr) 
    (u_i_ty : Expr)
    (u_i_ty_red : Expr)
    (inner : Expr)
    (rec_aux_result : list Expr)
    (indices_result : list Expr)
    (motive : Expr)
    (valid_pos : nat)
    (motive_appA : Expr)
    (v_i_ty : Expr)
    (serial : nat) :
    let rec_args := rec_args_hd:: rec_args_tl,
        self_idx' := self_idx + 1,
        v_name := Num (Str Anon ("v")) self_idx,
        motive := getInfal motives valid_pos,
        result_hd := mkLocal v_name v_i_ty Bstyle.Default serial,
        result := result_hd :: result_tl
    in
    handleRecArgsMinor rec_args_tl self_idx' result_tl 
    -> infer rec_args_hd InferOnly u_i_ty
    -> whnf u_i_ty u_i_ty_red
    -> handleRecArgsAux u_i_ty_red inner rec_aux_result
    -> getIIndices indblock inner valid_pos indices_result
    -> foldlApps motive indices_result motive_appA
    -> foldPis rec_aux_result motive_appA v_i_ty
    -> handleRecArgsMinor rec_args self_idx result


| stepDep
    (self_idx : nat)
    (rec_args_hd : Expr)
    (rec_args_tl : list Expr)
    (result_tl : list Expr) 
    (u_i_ty : Expr)
    (u_i_ty_red : Expr)
    (inner : Expr)
    (rec_aux_result : list Expr)
    (indices_result : list Expr)
    (motive : Expr)
    (valid_pos : nat)
    (motive_appA : Expr)
    (v_i_ty : Expr)
    (serial : nat)
    (u_app : Expr) :
    let rec_args := rec_args_hd:: rec_args_tl,
        self_idx' := self_idx + 1,
        v_name := Num (Str Anon ("v")) self_idx,
        motive := getInfal motives valid_pos,
        result_hd := mkLocal v_name v_i_ty Bstyle.Default serial,
        motive_appB := mkApp motive_appA u_app,
        result := result_hd :: result_tl
    in
    handleRecArgsMinor rec_args_tl self_idx' result_tl 
    -> infer rec_args_hd InferOnly u_i_ty
    -> whnf u_i_ty u_i_ty_red
    -> handleRecArgsAux u_i_ty_red inner rec_aux_result
    -> getIIndices 
          indblock
          inner 
          valid_pos 
          indices_result
    -> foldlApps motive indices_result motive_appA
    -> foldlApps rec_args_hd rec_aux_result u_app
    -> foldPis rec_aux_result motive_appB v_i_ty
    -> handleRecArgsMinor rec_args self_idx result


inductive mkMinorsGroup
    (indblock : CheckedIndblock)
    (motives : list Expr)
    (ind_name : Name)
    (ind_type : Expr)
    (ind_const : Expr)
    : ∀ (ctor_idx : nat)
        (rem_ctor_names : list Name)
        (rem_ctor_types : list Expr)
        (minors : list Expr),
        Prop

| base (ctor_idx : nat) :
    let rem_ctor_names : list Name := [],
        rem_ctor_types : list Expr := [],
        minors : list Expr := []
    in 
    mkMinorsGroup ctor_idx rem_ctor_names rem_ctor_types minors

| stepIndep
    (ctor_idx : nat)
    (ctor_names_hd : Name)
    (ctor_names_tl : list Name)
    (ctor_types_hd : Expr)
    (ctor_types_tl : list Expr)
    (minors_tl : list Expr)
    (all_args : list Expr)
    (rec_args : list Expr)
    (inner : Expr)
    (indices : list Expr)
    (valid_pos : nat)
    (motive : Expr)
    (c_appA : Expr)
    (v : list Expr)
    (minor_typeA : Expr)
    (minor_typeB : Expr)
    (minor_serial : nat) :
    let ctor_idx' := 1 + ctor_idx,
        rem_ctor_names := (ctor_names_hd :: ctor_names_tl),
        rem_ctor_types := (ctor_types_hd :: ctor_types_tl),
        motive := getInfal motives valid_pos,
        minor_name := Num (Str Anon "m") ctor_idx,
        minor := mkLocal minor_name minor_typeB Bstyle.Default minor_serial,
        minors := minor :: minors_tl
    in
    mkMinorsGroup ctor_idx' ctor_names_tl ctor_types_tl minors_tl
    -> sepCtorArgs indblock ind_type ind_const indblock.params ctor_types_hd  all_args rec_args inner
    -> getIIndices indblock inner valid_pos indices
    -> foldlApps motive indices c_appA
    -> handleRecArgsMinor indblock motives rec_args 0 v
    -> foldPis v c_appA minor_typeA
    -> foldPis all_args minor_typeA minor_typeB
    -> mkMinorsGroup ctor_idx rem_ctor_names rem_ctor_types minors

    
| stepDep
    (ctor_idx : nat)
    (ctor_names_hd : Name)
    (ctor_names_tl : list Name)
    (ctor_types_hd : Expr)
    (ctor_types_tl : list Expr)
    (minors_tl : list Expr)
    (all_args : list Expr)
    (rec_args : list Expr)
    (inner : Expr)
    (indices : list Expr)
    (valid_pos : nat)
    (motive : Expr)
    (c_appA : Expr)
    (v : list Expr)
    (minor_typeA : Expr)
    (minor_typeB : Expr)
    (minor_serial : nat)
    (rhsB : Expr)
    (rhsC : Expr) :
    let ctor_idx' := 1 + ctor_idx,
        rem_ctor_names := (ctor_names_hd :: ctor_names_tl),
        rem_ctor_types := (ctor_types_hd :: ctor_types_tl),
        motive := getInfal motives valid_pos,
        rhsA := mkConst ctor_names_hd indblock.uparams,
        c_appB := mkApp c_appA rhsC,
        minor_name := Num (Str Anon "m") ctor_idx,
        minor := mkLocal minor_name minor_typeB Bstyle.Default minor_serial,
        minors := minor :: minors_tl
    in
    mkMinorsGroup ctor_idx' ctor_names_tl ctor_types_tl minors_tl
    -> sepCtorArgs indblock ind_type ind_const indblock.params ctor_types_hd  all_args rec_args inner
    -> getIIndices indblock inner valid_pos indices
    -> foldlApps motive indices c_appA
    -> foldlApps rhsA indblock.params rhsB
    -> foldlApps rhsB all_args rhsC
    -> handleRecArgsMinor indblock motives rec_args 0 v
    -> foldPis v c_appB minor_typeA
    -> foldPis all_args minor_typeA minor_typeB
    -> mkMinorsGroup ctor_idx rem_ctor_names rem_ctor_types minors


inductive mkMinorsAux (indblock : CheckedIndblock) (motives : list Expr) :
  ∀ (ind_names : list Name)
    (ind_types : list Expr)
    (ind_consts : list Expr)
    (ctor_names : list Name)
    (ctor_types : list Expr)
    (minors : list Expr),
    Prop
| base :
    let ind_names : list Name := [],
        ind_types : list Expr := [],
        ind_consts : list Expr := [],
        ctor_names : list Name := [],
        ctor_types : list Expr := [],
        minors : list Expr := []
    in mkMinorsAux ind_names ind_types ind_consts ctor_names ctor_types minors

| step
    (ind_names_hd : Name)
    (ind_names_tl : list Name)
    (ind_types_hd : Expr)
    (ind_types_tl : list Expr)
    (ind_consts_hd : Expr)
    (ind_consts_tl : list Expr)
    (ctor_names_l : list Name)
    (ctor_names_r : list Name)
    (ctor_types_l : list Expr)
    (ctor_types_r : list Expr)
    (minors_l : list Expr)
    (minors_r : list Expr) :
    let ind_names := ind_names_hd :: ind_names_tl,
        ind_types := ind_types_hd :: ind_types_tl,
        ind_consts := ind_consts_hd :: ind_consts_tl,
        ctor_names := ctor_names_l ++ ctor_names_r,
        ctor_types := ctor_types_l ++ ctor_types_r,
        minors := minors_l ++ minors_r
    in 
    mkMinorsAux ind_names_tl ind_types_tl ind_consts_tl ctor_names_r ctor_types_r minors_r
    -> mkMinorsGroup 
            indblock
            motives
            ind_names_hd
            ind_types_hd
            ind_consts_hd
            1
            ctor_names_l
            ctor_types_l
            minors_l
    -> mkMinorsAux ind_names ind_types ind_consts ctor_names ctor_types minors

def mkMinors 
    (indblock : CheckedIndblock)
    (motives : list Expr)
    (all_minors : list Expr) 
    := mkMinorsAux
          indblock
          motives
          indblock.ind_names
          indblock.ind_types
          indblock.ind_consts
          indblock.ctor_names
          indblock.ctor_types
          all_minors
    
inductive getRecLevels 
    (indblock : CheckedIndblock) :  
    ∀ (elim_level : Level) 
      (rec_levels : list Level), Prop

| ofParam (n : Name) :
    let elim_level := Param n,
        rec_levels := elim_level :: indblock.uparams
    in mkElimLevel indblock elim_level
    -> getRecLevels elim_level rec_levels

| owise (elim_level : Level) :
    -- ASSERT : elim_level is not a Level.Param
    let rec_levels := indblock.uparams
    in
    mkElimLevel indblock elim_level
    -> getRecLevels elim_level rec_levels

 inductive handleRecRuleArgs
    (indblock : CheckedIndblock)
    (ind_name : Name)
    : ∀ (rec_args : list Expr)
        (rec_rule_parts : list Expr),
        Prop

| base :
    let rec_args : list Expr := [],
        rec_rule_parts : list Expr := []
    in handleRecRuleArgs rec_args rec_rule_parts

| step 
    (motives : list Expr)
    (minors : list Expr)
    (rec_args_hd : Expr)
    (rec_args_tl : list Expr)
    (rec_rule_parts_hd : Expr)
    (rec_rule_parts_tl : list Expr)
    (u_i_ty_unred : Expr)
    (u_i_ty_red : Expr)
    (u_i_ty : Expr)
    (u_i_ty : Expr)
    (xs : list Expr)
    (valid_app : nat)
    (indices : list Expr)
    (elim_level : Level)
    (rec_levels : list Level)
    (rec_appB : Expr)
    (rec_appC : Expr)
    (rec_appD : Expr)
    (rec_appE : Expr)
    (app_rhs : Expr) :
    let rec_args := rec_args_hd :: rec_args_tl,
        rec_rule_parts := rec_rule_parts_hd :: rec_rule_parts_tl,
        rec_name := Str ind_name "rec",
        rec_appA := mkConst rec_name rec_levels,
        made_app := mkApp rec_appE app_rhs
    in
    handleRecRuleArgs rec_args_tl rec_rule_parts_tl
    -> infer rec_args_hd InferOnly u_i_ty_unred
    -> whnf u_i_ty_unred u_i_ty_red
    -> handleRecArgsAux u_i_ty_red u_i_ty xs
    -> getIIndices indblock u_i_ty valid_app indices
    -> getRecLevels indblock elim_level rec_levels
    -> foldlApps rec_appA indblock.params rec_appB
    -> foldlApps rec_appB motives rec_appC
    -> foldlApps rec_appC minors rec_appD
    -> foldlApps rec_appD indices rec_appE
    -> foldlApps rec_args_hd xs app_rhs
    -> foldLambdas xs made_app rec_rule_parts_hd
    -> handleRecRuleArgs rec_args rec_rule_parts
    

inductive mkRecRule1
  (indblock : CheckedIndblock)
  (motives : list Expr)
  (ind_name : Name)
  (ind_type : Expr)
  (ind_const : Expr)
  (ctor_name : Name)
  (ctor_type : Expr)
  (minors_group : list Expr)
  (curr_minor : Expr) :
  ∀ (rec_rule : RecRule),
    Prop

| base 
  (all_args : list Expr)
  (rec_args : list Expr)
  (inner : Expr)
  (rec_rule_parts : list Expr)
  (rhsA : Expr)
  (rhsB : Expr)
  (rhsC : Expr)
  (rhsD : Expr)
  (rhsE : Expr)
  (rhsF : Expr)
  (tel_size : nat) :
    let num_fields := tel_size - indblock.num_params,
        rec_rule := RecRule.mk ctor_name num_fields rhsF
    in
    sepCtorArgs indblock ind_type ind_const indblock.params ctor_type all_args rec_args inner
    -> handleRecRuleArgs indblock ind_name rec_args rec_rule_parts
    -> foldlApps curr_minor all_args rhsA
    -> foldlApps rhsA rec_rule_parts rhsB
    -> foldLambdas all_args rhsB rhsC
    -> foldLambdas minors_group rhsC rhsD
    -> foldLambdas motives rhsD rhsE
    -> foldLambdas indblock.params rhsE rhsF
    -> telescopeSize ctor_type tel_size
    -> mkRecRule1 rec_rule

inductive mkRecRulesGroup
  (indblock : CheckedIndblock)
  (motives : list Expr)
  (ind_name : Name)
  (ind_type : Expr)
  (ind_const : Expr)
  (minors_group : list Expr)
  : ∀ (rem_ctor_names : list Name)
      (rem_ctor_types : list Expr)
      (rem_minors : list Expr)
      (rec_rules : list RecRule),
      Prop

| base :
  let rem_ctor_names : list Name := [],
      rem_ctor_types : list Expr := [],
      rem_minors : list Expr := [],
      rec_rules : list RecRule := []
  in mkRecRulesGroup rem_ctor_names rem_ctor_types rem_minors rec_rules
  
| step
  (rem_ctor_names_hd : Name)
  (rem_ctor_names_tl : list Name)
  (rem_ctor_types_hd : Expr)
  (rem_ctor_types_tl : list Expr)
  (rem_minors_hd : Expr)
  (rem_minors_tl : list Expr)
  (rec_rules_hd : RecRule)
  (rec_rules_tl : list RecRule) :
  let rem_ctor_names := rem_ctor_names_hd :: rem_ctor_names_tl,
      rem_ctor_types := rem_ctor_types_hd :: rem_ctor_types_tl,
      rem_minors := rem_minors_hd :: rem_minors_tl,
      rec_rules := rec_rules_hd :: rec_rules_tl
  in
  mkRecRulesGroup rem_ctor_names_tl rem_ctor_types_tl rem_minors_tl rec_rules_tl
  -> mkRecRule1 
          indblock 
          motives
          ind_name 
          ind_type 
          ind_const
          rem_ctor_names_hd
          rem_ctor_types_hd
          minors_group
          rem_minors_hd
          rec_rules_hd
    -> mkRecRulesGroup rem_ctor_names rem_ctor_types rem_minors rec_rules

inductive mkRecRules
  (indblock : CheckedIndblock)
  (all_motives : list Expr)
  : ∀ (ins : list Name)
      (its : list Expr)
      (ics : list Expr)
      (cns : list Name)
      (cts : list Expr)
      (minors : list Expr)
      (rec_rules : list RecRule),
      Prop
| base :
    let ins : list Name := [],
        its : list Expr := [],
        ics : list Expr := [],
        cns : list Name := [],
        cts : list Expr := [],
        minors : list Expr := [],
        rec_rules : list RecRule := []
    in  
    mkRecRules ins its ics cns cts minors rec_rules

| step
   (ins_hd : Name)
   (ins_tl : list Name)
   (its_hd : Expr)
   (its_tl : list Expr)
   (ics_hd : Expr)
   (ics_tl : list Expr)
   (cns_l : list Name)
   (cns_r : list Name)
   (cts_l : list Expr)
   (cts_r : list Expr)
   (minors_l : list Expr)
   (minors_r : list Expr)
   (rec_rules_l : list RecRule)
   (rec_rules_r : list RecRule) :
   let ins := ins_hd :: ins_tl,
       its := its_hd :: its_tl,
       ics := ics_hd :: ics_tl,
       cns := cns_l ++ cns_r,
       cts := cts_l ++ cts_r,
       minors := minors_l ++ minors_r,
       rec_rules := rec_rules_l ++ rec_rules_r
    in
    mkRecRules ins_tl its_tl ics_tl cns_r cts_r minors_r rec_rules_r
    -> mkRecRulesGroup indblock all_motives ins_hd its_hd ics_hd minors_l cns_l cts_l minors_l rec_rules_l
    -> mkRecRules ins its ics cns cts minors rec_rules

/-
These have literally one difference, which is whether the major premise
gets applied to the (motive + indices) combo
-/
inductive mkRecursorAux 
  (indblock : CheckedIndblock) 
  (ind_name : Name)
  (num_indices : nat)
  (k_target : bool) 
  (elim_level : Level)
  (all_motives : list Expr) 
  (motive : Expr)
  (major : Expr)
  (minors : list Expr)
  (rec_rules : list RecRule) :
  ∀ (recursor : Declar),
    Prop

| baseIndep 
    (motive_app : Expr)
    (tyA : Expr)
    (tyB : Expr)
    (tyC : Expr)
    (tyD : Expr)
    (rec_ty : Expr)
    (rec_uparams : list Level) :
    let 
        num_minors := minors.length,
        num_motives := all_motives.length,
        major_idx := indblock.num_params + num_indices + num_minors + num_motives,
        rec_name := Str ind_name "rec",
        recursor := Declar.Recursor rec_name rec_uparams rec_ty indblock.ind_names indblock.num_params num_indices num_motives num_minors major_idx rec_rules k_target indblock.is_unsafe
    in
    foldlApps motive indblock.indices motive_app
    -> applyPi major motive_app tyA
    -> foldPis indblock.indices tyA tyB
    -> foldPis minors tyB tyC
    -> foldPis all_motives tyC tyD
    -> foldPis indblock.params tyD rec_ty
    -> getRecLevels indblock elim_level rec_uparams
    -> mkRecursorAux recursor

 | baseDep 
    (motive_app_base : Expr)
    (tyA : Expr)
    (tyB : Expr)
    (tyC : Expr)
    (tyD : Expr)
    (rec_ty : Expr)
    (rec_uparams : list Level) :
    let 
        num_minors := minors.length,
        num_motives := all_motives.length,
        major_idx := indblock.num_params + num_indices + num_minors + num_motives,
        rec_name := Str ind_name "rec",
        motive_app := mkApp motive_app_base major,
        recursor := Declar.Recursor rec_name rec_uparams rec_ty indblock.ind_names indblock.num_params num_indices num_motives num_minors major_idx rec_rules k_target indblock.is_unsafe
    in
    foldlApps motive indblock.indices motive_app
    -> applyPi major motive_app tyA
    -> foldPis indblock.indices tyA tyB
    -> foldPis minors tyB tyC
    -> foldPis all_motives tyC tyD
    -> foldPis indblock.params tyD rec_ty
    -> getRecLevels indblock elim_level rec_uparams
    -> mkRecursorAux recursor   


inductive mkRecursors 
    (indblock : CheckedIndblock) 
    (all_motives : list Expr) 
    (k_target : bool)
    (elim_level : Level) :
    ∀ (ind_names : list Name)
      (motives : list Expr)
      (majors : list Expr)
      (indices : list Expr)
      (minors : list Expr)
      (rec_rules : list RecRule)
      (recursors : list Declar),
      Prop

| base :
  let ind_names : list Name := [],
      motives : list Expr := [],
      majors : list Expr := [],
      indices : list Expr := [],
      minors : list Expr := [],
      rec_rules : list RecRule := [],
      recursors : list Declar := []
  in
  mkRecursors ind_names motives majors indices minors rec_rules recursors

| step 
    (ind_names_hd : Name)
    (ind_names_tl : list Name)
    (motives_hd : Expr)
    (motives_tl : list Expr)
    (majors_hd : Expr)
    (majors_tl : list Expr)
    (indices_l : list Expr)
    (indices_r : list Expr)
    (minors_l : list Expr)
    (minors_r : list Expr)
    (rec_rules_l : list RecRule)
    (rec_rules_r : list RecRule)
    (recursors_hd : Declar)
    (recursors_tl : list Declar) :
    let
        num_indices := indices_l.length,
        ind_names := ind_names_hd :: ind_names_tl,
        motives := motives_hd :: motives_tl,
        majors := majors_hd :: majors_tl,
        indices := indices_l ++ indices_r,
        minors := minors_l ++ minors_r,
        rec_rules := rec_rules_l ++ rec_rules_r,
        recursors := recursors_hd :: recursors_tl
    in 
    mkRecursors 
        ind_names_tl 
        motives_tl 
        majors_tl 
        indices_r 
        minors_r 
        rec_rules_r 
        recursors_tl
    -> mkRecursorAux 
          indblock 
          ind_names_hd 
          num_indices 
          k_target
          elim_level
          all_motives 
          motives_hd 
          majors_hd 
          minors_l
          rec_rules_l
          recursors_hd
    -> mkRecursors
          ind_names
          motives
          majors
          indices
          minors
          rec_rules
          recursors

