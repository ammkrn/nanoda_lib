import 
  .name 
  .level 
  .expr
  .env

open Name Level Expr Declar Env

/-
In all locations where `env.getDeclar` gets used
in this file, the export file will show a pointer
to an `AdmitDeclar` step, which is the step at which
the given declaration was admitted to the current environment.

Also the reduction steps for quotient don't contain
any explicit assertion that quotient has been admitted
to the environment, though the implementation does.
-/


def qmk_name : Name := Str (Str Anon "quot") "mk"
def qlift_name : Name := Str (Str Anon "quot") "lift"
def qind_name : Name := Str (Str Anon "quot") "ind"

inductive InferFlag
| Check
| InferOnly

instance : decidable_eq InferFlag := by tactic.mk_dec_eq_instance

inductive DeltaResult
| DeltaEq
| Exhausted : Expr -> Expr -> DeltaResult

open InferFlag DeltaResult


inductive unfoldDef : ∀ (e unfolded : Expr), Prop
| base 
    (env : Env)
    (e : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (args : list Expr)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_val : Expr)
    (d_val' : Expr)
    (unfolded : Expr) :
    let base := mkConst c_name c_levels,
        d_view := DeclarView.mk c_name d_uparams d_type (some d_val)
    in
    -- ASSERT : c_levels.length = d_uparams.length
    unfoldApps e (base, args)
    -> env.getDeclarView c_name d_view
    -> subst d_val d_uparams c_levels d_val'
    -> foldlApps d_val' args unfolded
    -> unfoldDef e unfolded

inductive mkNullaryCtor : Expr -> Expr -> Prop
| base 
    (env : Env)
    (e : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (args : list Expr)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_num_params : nat)
    (d_ind_names : list Name)
    (d_ctor_names : list Name)
    (d_is_unsafe : bool)
    (out : Expr) :
    let base := mkConst c_name c_levels,
        zth_ctor_name := getInfal d_ctor_names 0,
        fold_args := args.take d_num_params,
        ind := Inductive c_name d_uparams d_type d_num_params d_ind_names d_ctor_names d_is_unsafe,
        fold_const := mkConst zth_ctor_name c_levels
    in
    unfoldApps e (base, args)
    -> env.getDeclar c_name (Inductive c_name d_uparams d_type d_num_params d_ind_names d_ctor_names d_is_unsafe)
    -> foldlApps fold_const fold_args out
    -> mkNullaryCtor e out

mutual inductive 
    whnf,
    whnfCore,
    whnfSort,
    whnfLambda,
    whnfLet,
    reduceQuotLift,
    reduceQuotInd,
    toCtorWhenK,
    reduceIndRec,
    defEq,
    isSortZero,
    isProposition,
    isProof,
    proofIrrelEq,
    defEqSort,
    defEqPi,
    defEqLambda,
    argsEqAux,
    lazyDeltaStep,
    defEqConst,
    defEqLocal,
    defEqApp,
    defEqEta,
    infer,
    inferSortOf,
    ensureSort,
    ensureType,
    ensurePi,
    inferSort,
    inferConst,
    inferApp,
    inferPi,
    inferLambda,
    inferLet,
    inferLocal
       

with whnf : ∀ (e e' : Expr), Prop
| coreOnly (e e' : Expr) : whnfCore e e' -> whnf e e'
| unfolding (e cored unfolded e' : Expr) :
    whnfCore e cored
    -> unfoldDef cored unfolded
    -> whnf unfolded e'
    -> whnf e e'

with whnfCore : ∀ (e e' : Expr), Prop
| sort (e e' : Expr) : whnfSort e e' -> whnfCore e e'

| lambda 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr) :
    unfoldApps e (f, args)
    -> whnfLambda f args [] e'
    -> whnfCore e e'

| let_ 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr) :
    unfoldApps e (f, args)
    -> whnfLet f args e'
    -> whnfCore e e'

| quotLift 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr) :
    unfoldApps e (f, args)
    -> reduceQuotLift f args e'
    -> whnfCore e e'

| quotInd 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr) :
    unfoldApps e (f, args)
    -> reduceQuotInd f args e'
    -> whnfCore e e'

| indRec 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr) :
    unfoldApps e (f, args)
    -> reduceIndRec f args e'
    -> whnfCore e e'

with whnfSort : ∀ (s s' : Expr), Prop
| sort (l l' : Level ) : 
    let s := mkSort l,
        s' := mkSort l'
    in
    simplify l l' -> whnfSort s s'

-- The lambda and args have already been unfolded by whnfCore
with whnfLambda : 
    ∀ (lambda : Expr)
      (rem_args : list Expr)
      (lambda_args : list Expr)
      (e' : Expr),
      Prop
| notLambda 
    (eA : Expr)
    (rem_args : list Expr)
    (lambda_args : list Expr)
    (eB eC eD : Expr) :
    isLambda eA ff
    -> inst eA lambda_args eB
    -> foldlApps eB rem_args eC
    -> whnfCore eC eD
    -> whnfLambda eA rem_args lambda_args eD

| noArgs 
    (eA : Expr)
    (lambda_args : list Expr)
    (eB : Expr) 
    (eC : Expr) : 
    let all_args : list Expr := []
    in
    inst eA lambda_args eB
    -> whnfCore eB eC
    -> whnfLambda eA all_args lambda_args eC

| step 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (arg_hd : Expr)
    (args_tl : list Expr)
    (lambda_args : list Expr)
    (b' : Expr) :
    let lambda := mkLambda n t s b,
        lambda_args' := arg_hd :: lambda_args,
        all_args := arg_hd :: args_tl
    in
    whnfLambda b args_tl lambda_args' b'
    -> whnfLambda b all_args lambda_args b'

with whnfLet : ∀ (e : Expr) (args : list Expr) (e' : Expr), Prop      
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (bodyA : Expr)
    (args : list Expr)
    (bodyB : Expr)
    (bodyC : Expr)
    (e' : Expr) : 
    let e := mkLet n t s v bodyA
    in
    inst1 bodyA v bodyB
    -> foldlApps bodyB args bodyC
    -> whnfCore bodyC e'
    -> whnfLet e args e'

/-
For the quot reduction steps, qlift_name, qind_name, qmk_pos, f_pos, and B_of_pos
are not going to be present in the output since they're literal constants.
-/
with reduceQuotLift : ∀ (constE : Expr) (args : list Expr) (out : Expr), Prop
| base 
    (c_levels : list Level)
    (args : list Expr)
    (qmk_A_r : Expr)
    (a : Expr)
    (qmk_levels : list Level)
    (qmk_args : list Expr)
    (out_unred : Expr)
    (out : Expr) :
    let qmk_pos := 5,
        f_pos := 3,
        skipped := args.drop (qmk_pos + 1),
        qmk_const := mkConst qmk_name qmk_levels,
        qlift_const := mkConst qlift_name c_levels,
        qmk_A_r_a_unred := getInfal args qmk_pos,
        qmk_A_r_a := mkApp qmk_A_r a,
        f := getInfal args f_pos,
        B := mkApp f a
    in
    -- ASSERT : quot is defined/exists in env
    whnf qmk_A_r_a_unred qmk_A_r_a
    -> unfoldApps qmk_A_r_a (qmk_const, qmk_args)
    -> foldlApps B skipped out_unred
    -> whnfCore out_unred out
    -> reduceQuotLift qlift_const args out

with reduceQuotInd : ∀ (constE : Expr) (args : list Expr) (out : Expr), Prop
| base 
    (c_levels : list Level)
    (args : list Expr)
    (qmk_A_r : Expr)
    (a : Expr)
    (qmk_levels : list Level)
    (qmk_args : list Expr)
    (B_of : Expr)
    (out_unred : Expr)
    (out : Expr) :
    let qmk_pos := 4,
        B_of_pos := 3,
        skipped := args.drop (qmk_pos + 1),
        qmk_const := mkConst qmk_name qmk_levels,
        qind_const := mkConst qind_name c_levels,
        B_of := getInfal args B_of_pos,
        qmk_A_r_a_unred := getInfal args qmk_pos,
        qmk_A_r_a := mkApp qmk_A_r a,
        B_app := mkApp B_of a
    in
    -- ASSERT : Quot is defined/exists in env
    whnf qmk_A_r_a_unred qmk_A_r_a
    -> unfoldApps qmk_A_r_a (qmk_const, qmk_args)
    -> foldlApps B_app skipped out_unred
    -> whnfCore out_unred out
    -> reduceQuotInd qind_const args out

with toCtorWhenK : Expr -> Declar -> Expr -> Prop
| skip (e : Expr) (d : Declar) : toCtorWhenK e d e

| base 
    (e : Expr)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_names : list Name)
    (d_num_params : nat)
    (d_num_indices : nat)
    (d_num_motives : nat)
    (d_num_minors : nat)
    (d_major_idx : nat)
    (d_rec_rules : list RecRule)
    (d_is_k : bool)
    (d_is_unsafe : bool)
    (e_type_unred : Expr)
    (e_type : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (c_args : list Expr)
    (ctor_app : Expr)
    (ctor_app_type : Expr) :
    -- ASSERT : d_is_k = tt
    let const := mkConst c_name c_levels,
        recursor := 
          Recursor 
          (Str c_name "rec") 
          d_uparams 
          d_type 
          d_names 
          d_num_params 
          d_num_indices 
          d_num_motives 
          d_num_minors 
          d_major_idx 
          d_rec_rules 
          tt 
          d_is_unsafe
    in
    infer e InferOnly e_type_unred
    -> whnf e_type_unred e_type
    -> unfoldApps e_type (const, c_args)
    -> mkNullaryCtor e_type ctor_app
    -> infer ctor_app InferOnly ctor_app_type
    -> defEq e_type ctor_app_type
    -> toCtorWhenK e recursor ctor_app


with reduceIndRec : Expr -> list Expr -> Expr -> Prop
| base 
    (env : Env)
    (c_name : Name)
    (c_levels : list Level)
    (args : list Expr)
    -- Recursor info : recursor's name is c_name
    (d_uparams : list Level)
    (d_type : Expr)
    (d_names : list Name)
    (d_num_params : nat)
    (d_num_indices : nat)
    (d_num_motives : nat)
    (d_num_minors : nat)
    (d_major_idx : nat)
    (d_rec_rules : list RecRule)
    (d_is_k : bool)
    (d_is_unsafe : bool)       
    -- 
    (major_unredB : Expr)
    (major_name : Name)
    (major_levels : list Level)
    (major_args : list Expr)
    (major : Expr)
    -- rec_rule info
    (rr_ctor_name : Name)
    (rr_num_fields : nat)
    (rr_val : Expr)
    --
    (major_args_len : nat)
    (r6 : Expr)
    (r7 : Expr)
    (r8 : Expr)
    (r9 : Expr)
    (r10 : Expr) :
    let 
    -- assert : major_args.len = major_args_len
    base_const := mkConst c_name c_levels,
    major_unredA := getInfal args d_major_idx,
    major_fun := mkConst major_name major_levels,
    got_rec_rule := RecRule.mk rr_ctor_name rr_num_fields rr_val,
    skip1 := major_args.drop (major_args_len - rr_num_fields),
    skip2 := args.drop (1 + d_major_idx),
    take1 := skip1.take rr_num_fields,
    take2 := args.take (d_num_params + d_num_motives + d_num_minors),
    recursor := 
        Recursor 
        c_name
        d_uparams 
        d_type 
        d_names 
        d_num_params 
        d_num_indices 
        d_num_motives 
        d_num_minors 
        d_major_idx 
        d_rec_rules 
        d_is_k
        d_is_unsafe
    in       
    env.getDeclar c_name recursor
    -> toCtorWhenK major_unredA recursor major_unredB
    -> whnf major_unredB major
    -> unfoldApps major (major_fun, major_args)
    -> getRecRule d_rec_rules major_name got_rec_rule
    -> subst rr_val d_uparams c_levels r6
    -> foldlApps r6 take2 r7
    -> foldlApps r7 take1 r8
    -> foldlApps r8 skip2 r9
    -> whnfCore r9 r10
    -> reduceIndRec base_const args r10
     
with defEq : Expr -> Expr -> Prop
| reflexivity (e : Expr) : defEq e e
| sort 
    (l r : Expr) 
    (l_w r_w : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> defEqSort l_w r_w
    -> defEq l r

| pi 
    (l r : Expr)
    (l_w r_w : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> defEqPi l_w r_w []
    -> defEq l r

| lambda 
    (l r : Expr)
    (l_w r_w : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> defEqLambda l_w r_w []
    -> defEq l_w r_w

| proofIrrel 
    (l r : Expr)
    (l_w r_w : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> proofIrrelEq l_w r_w
    -> defEq l r

| deltaEq 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w DeltaEq
    -> defEq l r

| eqConst 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w (Exhausted l_d r_d)
    -> defEqConst l_d r_d
    -> defEq l r

| eqLocal 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w (Exhausted l_d r_d)
    -> defEqLocal l_d r_d
    -> defEq l r

| eqApp 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w (Exhausted l_d r_d)
    -> defEqApp l_d r_d
    -> defEq l r

| etaLr 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w (Exhausted l_d r_d)
    -> defEqEta l_d r_d
    -> defEq l r

| etaRl 
    (l r : Expr)
    (l_w r_w : Expr)
    (l_d r_d : Expr)
    : whnfCore l l_w
    -> whnfCore r r_w
    -> lazyDeltaStep r_w r_w (Exhausted l_d r_d)
    -> defEqEta r_d l_d
    -> defEq l r
        

with isSortZero : Expr -> Prop
| base (e : Expr) : 
  let z := mkSort Zero
  in 
  whnf e z 
  -> isSortZero e

with isProposition : Expr -> Expr -> Prop
| base (e inferred : Expr) :
    infer e InferOnly inferred
    -> isSortZero inferred
    -> isProposition e inferred

with isProof : Expr -> Expr -> Prop
| base (e inferred sort_of : Expr) :
    infer e InferOnly inferred
    -> isProposition inferred sort_of
    -> isProof e inferred

with proofIrrelEq : Expr -> Expr -> Prop
| base 
    (l r : Expr)
    (l_type r_type : Expr) :
    isProof l l_type
    -> isProof r r_type
    -> defEq l_type r_type
    -> proofIrrelEq l_type r_type

with defEqSort : Expr -> Expr -> Prop
| base (l r : Level) :
  let e1 := mkSort l,
      e2 := mkSort r
  in
  eqAntisymm l r tt
  -> defEqSort e1 e2

with defEqPi : Expr -> Expr -> list Expr -> Prop
| base 
    (l r : Expr)
    (doms : list Expr)
    (l' r' : Expr)
    : isPi l ff
    -> isPi r ff
    -> inst l doms l'
    -> inst r doms r'
    -> defEq l' r'
    -> defEq l r
    -> defEqPi l r doms

| step 
    (ln rn : Name)
    (lt rt : Expr)
    (ls rs : Bstyle)
    (lb rb : Expr)
    (lt' rt' : Expr)
    (doms : list Expr)
    (serial : nat) :
    let local_expr := mkLocal ln lt' ls serial,
        doms' := local_expr :: doms,
        e1 := mkPi ln lt ls lb,
        e2 := mkPi rn rt rs rb
    in
    inst lt doms lt'
    -> inst rt doms rt'
    -> defEq lt' rt'
    -> defEqPi lb rb doms' 
    -> defEqPi e1 e2 doms


with defEqLambda : Expr -> Expr -> list Expr -> Prop
| base 
    (l r : Expr)
    (doms : list Expr)
    (l' r' : Expr) :
    isLambda l ff
    -> isLambda r ff
    -> inst l doms l'
    -> inst r doms r'
    -> defEq l' r'
    -> defEq l r
    -> defEqLambda l r doms

| step 
    (ln rn : Name)
    (lt rt : Expr)
    (ls rs : Bstyle)
    (lb rb : Expr)
    (lt' rt' : Expr)
    (doms : list Expr)
    (serial : nat) :
    let local_expr := mkLocal ln lt' ls serial,
        doms' := local_expr :: doms,
        e1 := mkLambda ln lt ls lb,
        e2 := mkLambda rn rt rs rb
    in
        
    inst lt doms lt'
    -> inst rt doms rt'
    -> defEq lt' rt'
    -> defEqLambda lb rb doms'
    -> defEqLambda e1 e2 doms

-- there is no ArgsEq in the spec, but this lets me keep the names sync'd
with argsEqAux : ∀ (l r : list Expr), Prop
-- This also covers the base case of nil nil since
-- they'll be equal identifiers
| refl (l r : list Expr) : 
    -- ASSERT : l = r (identical index #s)
    argsEqAux l r
| step 
    (l_hd : Expr)
    (r_hd : Expr)
    (l_tl : list Expr)
    (r_tl : list Expr) :
    let l := l_hd :: l_tl,
        r := r_hd :: r_tl
    in
    defEq l_hd r_hd
    -> argsEqAux l_tl r_tl
    -> argsEqAux l r

with lazyDeltaStep : Expr -> Expr -> DeltaResult -> Prop
| eqSort (l r : Expr) : defEqSort l r -> lazyDeltaStep l r DeltaEq
| eqPi (l r : Expr) : defEqPi l r [] -> lazyDeltaStep l r DeltaEq
| eqLambda (l r : Expr) : defEqLambda l r [] -> lazyDeltaStep l r DeltaEq
| neither (l r : Expr) : lazyDeltaStep l r (Exhausted l r)
| unfoldingLeft
    (l : Expr)
    (r :Expr)
    (l_defval_unred : Expr)
    (l_defval : Expr)
    (result : DeltaResult) :
    unfoldDef l l_defval_unred
    -> whnfCore l_defval_unred l_defval
    -> lazyDeltaStep l_defval r result
    -> lazyDeltaStep l r result
           
| unfoldingRight 
    (l : Expr)
    (r : Expr)
    (r_defval_unred : Expr)
    (r_defval : Expr)
    (result : DeltaResult) :
    unfoldDef r r_defval_unred
    -> whnfCore r_defval_unred r_defval
    -> lazyDeltaStep l r_defval result
    -> lazyDeltaStep l r result

| extensional 
    (l : Expr)
    (r : Expr)
    (c_name : Name)
    (l_clevels r_clevels : list Level)
    (l_args r_args : list Expr) :
    let l_const := mkConst c_name l_clevels,
        r_const := mkConst c_name r_clevels
    in
    unfoldApps l (l_const, l_args)
    -> unfoldApps r (r_const, r_args)
    -> argsEqAux l_args r_args
    -> eqAntisymmMany l_clevels r_clevels tt
    -> lazyDeltaStep l r DeltaEq

| unfoldingBoth
    (l r : Expr)
    (l_defval_unred : Expr)
    (r_defval_unred : Expr)
    (l_defval : Expr)
    (r_defval : Expr)
    (result : DeltaResult) :
    unfoldDef l l_defval_unred
    -> unfoldDef r r_defval_unred
    -> whnfCore l_defval_unred l_defval
    -> whnfCore r_defval_unred r_defval
    -> lazyDeltaStep r_defval l_defval result
    -> lazyDeltaStep l r result
          
with defEqConst : Expr -> Expr -> Prop
| base 
    (n : Name)
    (l_levels r_levels : list Level) :
    let e1 := mkConst n l_levels,
        e2 := mkConst n r_levels
    in
    eqAntisymmMany l_levels r_levels tt
    -> defEqConst e1 e2

-- Any time two Locals have the same serial, they (should be) guaranteed
-- to be identical.
with defEqLocal : Expr -> Expr -> Prop
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat) :
    let e := mkLocal n t s serial
    in
    defEqLocal e e

with defEqApp : Expr -> Expr -> Prop
| base 
    (l r : Expr)
    (l_fun r_fun : Expr)
    (l_args r_args : list Expr) :
    unfoldApps l (l_fun, l_args)
    -> unfoldApps r (r_fun, r_args)
    -> defEq l_fun r_fun
    -> argsEqAux l_args r_args
    -> defEqApp l r

with defEqEta : Expr -> Expr -> Prop
| base 
    (r : Expr)
    (ln rn : Name)
    (lt rt : Expr)
    (ls rs : Bstyle)
    (lb rb : Expr)
    (r_type_unred : Expr) :
    let r_type_red := mkPi rn rt rs rb,
        l_lambda := mkLambda ln lt ls lb,
        r_lambda := mkLambda rn rt rs (mkApp r (mkVar 0))
    in
    infer r InferOnly r_type_unred
    -> whnf r_type_unred r_type_red
    -> defEq l_lambda r_lambda 
    -> defEqEta l_lambda r

with infer : Expr -> InferFlag -> Expr -> Prop
| sort 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr) :
    inferSort e flag inferred
    -> infer e flag inferred

| const 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr) :
    inferConst e flag inferred
    -> infer e flag inferred

| app 
    (e : Expr) 
    (flag : InferFlag)
    (f : Expr)
    (args : list Expr)
    (f_type : Expr)
    (inferred : Expr) :
    unfoldApps e (f, args)
    -> infer f flag f_type
    -> inferApp f_type args [] flag inferred
    -> infer e flag inferred

| pi 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    : inferPi e [] [] flag inferred
    -> infer e flag inferred
     
| lambda 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr) :
    inferLambda e [] [] flag inferred
    -> infer e flag inferred

| let_ (e : Expr)
       (flag : InferFlag)
       (inferred : Expr) :
       inferLet e flag inferred
       -> infer e flag inferred

| local_ 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr) :
    inferLocal e flag inferred
    -> infer e flag inferred
      

with inferSortOf : Expr -> InferFlag -> Level -> Prop
| base 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    (l : Level) :
    let e' := mkSort l
    in
    infer e flag inferred
    -> whnf inferred e'
    -> inferSortOf e flag l

with ensureSort : Expr -> Level -> Prop
| base (l : Level) : 
    let e := mkSort l
    in
    ensureSort e l
| step 
    (e : Expr)
    (l : Level) :
    let e' := mkSort l
    in
    whnf e e'
    -> ensureSort e l

with ensureType : Expr -> Level -> Prop
| base 
    (e : Expr)
    (e_type : Expr)
    (l : Level) :
    infer e InferOnly e_type
    -> ensureSort e_type l
    -> ensureType e l

with ensurePi : Expr -> Expr -> Prop
| base (e : Expr) : isPi e tt -> ensurePi e e
| step (e e' : Expr) : whnf e e' -> isPi e' tt -> ensurePi e e'
       

with inferSort : Expr -> InferFlag -> Expr -> Prop
| inferOnly (l : Level) : 
    let e := mkSort l,
        e' := mkSort (Succ l)
    in
    inferSort e InferOnly e'
| checked 
    (l : Level) 
    (tc_uparams : list Level) :
    let e := mkSort l,
        e' := mkSort (Succ l)
    in
    paramsDefined l tc_uparams
    -> inferSort e Check e'
            
 


with inferConst : Expr -> InferFlag -> Expr -> Prop
| inferOnly 
    (env : Env)
    (c_name : Name)
    (c_levels : list Level)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_val : option Expr)
    (inferred : Expr):
    let flag := InferOnly,
        e := mkConst c_name c_levels,
        declar_view := DeclarView.mk c_name d_uparams d_type d_val
    in
    env.getDeclarView c_name declar_view
    -> subst d_type d_uparams c_levels inferred
    -> inferConst e flag inferred

       
-- tc_uparams is the set of universe parameters from the
-- declaration currently being checked by the type checker.
| check 
    (env : Env)
    (c_name : Name)
    (c_levels : list Level)
    (tc_uparams : list Level)
    (d : Declar)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_val : option Expr)
    (inferred : Expr) :
    let flag := Check,
        e := mkConst c_name c_levels,
        declar_view := DeclarView.mk c_name d_uparams d_type d_val
    in
    env.getDeclarView c_name declar_view
    -> paramsDefinedMany c_levels tc_uparams
    -> subst d_type d_uparams c_levels inferred
    -> inferConst e flag inferred


with inferApp : Expr -> list Expr -> list Expr -> InferFlag -> Expr -> Prop
-- looks weird since the function body's type was inferred
-- before we star using inferApp in order to prevent the need
-- for an auxiliary function.
| base 
    (e : Expr)
    (context : list Expr)
    (flag : InferFlag)
    (inferred : Expr) :
    inst e context inferred
    -> inferApp e [] context flag inferred

| stepInferOnly 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (hd : Expr)
    (args_tl : list Expr)
    (context : list Expr)
    (inferred : Expr) :
    let e := mkPi n t s b,
        args := hd :: args_tl,
        context' := hd :: context
    in
    inferApp b args_tl context' InferOnly inferred
    -> inferApp e args (context) InferOnly inferred

| stepChecked   
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (hd : Expr)
    (args_tl : list Expr)
    (context : list Expr)
    (t' : Expr)
    (arg_type : Expr)
    (inferred : Expr) :
    let e := mkPi n t s b,
        context' := hd :: context,
        args := hd :: args_tl
    in
    inst t context t'
    -> infer hd Check arg_type
    -> defEq t' arg_type
    -> inferApp b args_tl context' Check inferred
    -> inferApp e args context Check inferred

| stepNotPi 
    (e : Expr)
    (e' : Expr)
    (args : list Expr)
    (context : list Expr)
    (flag : InferFlag)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (inferred : Expr) :
    let as_pi := mkPi n t s b
    in
    inst e context e'
    -> ensurePi e' as_pi
    -> inferApp as_pi args [] flag inferred
    -> inferApp e args context flag inferred

with inferPi : Expr -> list Expr -> list Level -> InferFlag -> Expr -> Prop
| base 
    (e : Expr)
    (local_binders : list Expr)
    (levels : list Level)
    (flag : InferFlag)
    (inferred : Expr)
    (instd : Expr)
    (inferred_level : Level)
    (folded : Level) :
    isPi e ff
    -> inst e local_binders instd
    -> inferSortOf instd flag inferred_level
    -> foldImaxs levels inferred_level folded
    -> inferPi e local_binders levels flag (mkSort folded)

| step 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (local_binders : list Expr)
    (levels : list Level)
    (flag : InferFlag)
    (inferred : Expr)
    (t' : Expr)
    (inferred_level : Level)
    (serial : nat) :
    let e := mkPi n t s b,
        levelsA := inferred_level :: levels,
        local_expr := mkLocal n t' s serial,
        localsA := local_expr :: local_binders
    in
    inst t local_binders t'
    -> inferSortOf t' flag inferred_level
    -> inferPi b localsA levelsA flag inferred
    -> inferPi e local_binders levels flag inferred


with inferLambda : Expr -> list Expr -> list Expr -> InferFlag -> Expr -> Prop
| base 
    (e : Expr)
    (b_types : list Expr)
    (local_binders : list Expr)
    (flag : InferFlag)
    (inferred : Expr)
    (e' : Expr)
    (inferred_inner : Expr)
    (abstrd : Expr)
    (folded : Expr) :
    isLambda e ff
    -> inst e local_binders e'
    -> infer e' flag inferred_inner
    -> abstr inferred_inner local_binders abstrd
    -> foldPisOnce b_types local_binders abstrd folded
    -> inferLambda e b_types local_binders flag folded

| stepInferOnly 
    (n : Name)       
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (b_types : list Expr)
    (local_binders : list Expr)
    (t' : Expr)
    (inferred : Expr)
    (serial : nat) :
    let e := mkLambda n t s b,
        local_expr := mkLocal n t' s serial,
        b_typesA := t :: b_types,
        localsA := local_expr :: local_binders
    in
    inst t local_binders t'
    -> inferLambda b b_typesA localsA InferOnly inferred
    -> inferLambda e b_types local_binders InferOnly inferred

       
| stepChecked 
    (n : Name)       
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (b_types : list Expr)
    (local_binders : list Expr)
    (inferred : Expr)
    (t' : Expr)
    (b_type_sort : Level)
    (serial : nat) :
    let e := mkLambda n t s b,
        local_expr := mkLocal n t' s serial,
        b_typesA := t :: b_types,
        localsA := local_expr :: local_binders
    in
    inst t local_binders t'
    -> inferSortOf t' Check b_type_sort
    -> inferLambda b b_typesA localsA Check inferred
    -> inferLambda e b_types local_binders Check inferred


with inferLet : Expr -> InferFlag -> Expr -> Prop
| inferOnly 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (b' : Expr)
    (inferred : Expr) :
    let e := mkLet n t s v b
    in
    inst1 b v b'
    -> infer b' InferOnly inferred
    -> inferLet e InferOnly inferred

| checked 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (t_level : Level)
    (v_type : Expr)
    (b' : Expr)
    (inferred : Expr) :
    let e := mkLet n t s v b
    in
    inferSortOf t Check t_level
    -> infer v Check v_type
    -> defEq v_type t
    -> inst1 b v b'
    -> infer b' Check inferred
    -> inferLet e Check inferred

with inferLocal : ∀ (e : Expr) (flag : InferFlag) (t : Expr), Prop
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (flag : InferFlag) :
    let e := mkLocal n t s serial
    in 
    inferLocal e flag t
