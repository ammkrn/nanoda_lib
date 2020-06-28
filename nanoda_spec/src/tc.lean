import .name 
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
to the environment as of now.
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


inductive unfoldDef : Expr -> Expr -> Prop
| base 
    (env : Env)
    (e : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (args : list Expr)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_val : Expr)
    (d_hint : Hint)
    (d_is_unsafe : bool)
    (uparams_len : nat)
    (d_val' : Expr)
    (e' : Expr)
    :
    unfoldApps e (mkConst c_name c_levels) args
    -> env.getDeclar c_name (Definition c_name d_uparams d_type d_val d_hint d_is_unsafe)
    -> listLen c_levels uparams_len
    -> listLen d_uparams uparams_len
    -> subst d_val d_uparams c_levels d_val'
    -> foldlApps d_val' args e'
    -> unfoldDef e e'

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
    (zth_ctor_name : Name)
    (taken : list Expr)
    (out : Expr)
    : unfoldApps e (mkConst c_name c_levels) args
    -> env.getDeclar c_name (Inductive c_name d_uparams d_type d_num_params d_ind_names d_ctor_names d_is_unsafe)
    -> listGet d_ctor_names 0 zth_ctor_name
    -> listTake args d_num_params taken
    -> foldlApps (mkConst zth_ctor_name c_levels) taken out
    -> mkNullaryCtor e out

inductive isDelta : Expr -> Declar -> Prop
| base 
    (env : Env)
    (e : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (args : list Expr)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_val : Expr)
    (d_hint : Hint)
    (d_is_unsafe : bool)
    : let defn := Definition c_name d_uparams d_type d_val d_hint d_is_unsafe
    in
    unfoldApps e (mkConst c_name c_levels) args
    -> env.getDeclar c_name (Definition c_name d_uparams d_type d_val d_hint d_is_unsafe)
    -> isDelta e (defn)





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
    argsEq,
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
       

with whnf : Expr -> Expr -> Prop
| coreOnly (e e' : Expr) : whnfCore e e' -> whnf e e'
| unfolding (eA eB eC eD : Expr)
    : whnfCore eA eB
    -> unfoldDef eB eC
    -> whnf eC eD
    -> whnf eA eD

with whnfCore : Expr -> Expr -> Prop
| sort (e e' : Expr) : whnfSort e e' -> whnfCore e e'

| lambda 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr)
    : unfoldApps e f args
    -> whnfLambda f args [] e'
    -> whnfCore e e'

| let_ 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr)
    : unfoldApps e f args
    -> whnfLet f args e'
    -> whnfCore e e'

| quotLift 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr)
    : unfoldApps e f args
    -> reduceQuotLift f args e'
    -> whnfCore e e'

| quotInd 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr)
    : unfoldApps e f args
    -> reduceQuotInd f args e'
    -> whnfCore e e'

| indRec 
    (e : Expr)
    (f : Expr)
    (args : list Expr)
    (e' : Expr)
    : unfoldApps e f args
    -> reduceIndRec f args e'
    -> whnfCore e e'

with whnfSort : Expr -> Expr -> Prop
| sort (l l' : Level ): simplify l l' -> whnfSort (mkSort l) (mkSort l')

with whnfLambda : Expr -> list Expr -> list Expr -> Expr -> Prop
| notLambda 
    (eA : Expr)
    (rem_args : list Expr)
    (lambda_args : list Expr)
    (eB eC eD : Expr)
    : isLambda eA ff
    -> inst eA lambda_args eB
    -> foldlApps eB rem_args eC
    -> whnfCore eC eD
    -> whnfLambda eA rem_args lambda_args eD

| noArgs 
    (eA : Expr)
    (lambda_args : list Expr)
    (eB eC : Expr)
    : inst eA lambda_args eB
    -> whnfCore eB eC
    -> whnfLambda eA [] lambda_args eC

| step 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (arg_hd : Expr)
    (args_tl : list Expr)
    (lambda_args : list Expr)
    (b' : Expr)
    : whnfLambda b args_tl (arg_hd :: lambda_args) b'
    -> whnfLambda b (arg_hd :: args_tl) lambda_args b'

with whnfLet : Expr -> list Expr -> Expr -> Prop      
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (bodyA : Expr)
    (args : list Expr)
    (bodyB bodyC bodyD : Expr)
    : 
    inst1 bodyA v bodyB
    -> foldlApps bodyB args bodyC
    -> whnfCore bodyC bodyD
    -> whnfLet (mkLet n t s v bodyA) args bodyD

with reduceQuotLift : Expr -> list Expr -> Expr -> Prop
| base 
    (c_levels : list Level)
    (args : list Expr)
    (qmk_A_r_a_unred : Expr)
    (qmk_A_r : Expr)
    (a : Expr)
    (qmk_levels : list Level)
    (qmk_args : list Expr)
    (f : Expr)
    (skipped : list Expr)
    (out_unred : Expr)
    (out : Expr)
    : let qmk_pos := 5,
        f_pos := 3
    in
    -- assert that quotient has been declared with
    -- env.getDeclar c_name (Definition <quot stuff>)
    listGet args qmk_pos qmk_A_r_a_unred
    -> whnf qmk_A_r_a_unred (mkApp qmk_A_r a)
    -> unfoldApps (mkApp qmk_A_r a) (mkConst qmk_name qmk_levels) qmk_args
    -> listGet args f_pos f
    -> listSkip args (qmk_pos + 1) skipped
    -> foldlApps (mkApp f a) skipped out_unred
    -> whnfCore out_unred out
    -> reduceQuotLift (mkConst qlift_name c_levels) args out

with reduceQuotInd : Expr -> list Expr -> Expr -> Prop
| base 
    (c_levels : list Level)
    (args : list Expr)
    (qmk_A_r_a_unred : Expr)
    (qmk_A_r : Expr)
    (a : Expr)
    (qmk_levels : list Level)
    (qmk_args : list Expr)
    (B_of : Expr)
    (skipped : list Expr)
    (out_unred : Expr)
    (out : Expr)
    :
    let qmk_pos := 4,
        B_of_pos := 3
    in
       -- assert that quotient has been declared with
       -- env.getDeclar c_name (Definition <quot stuff>)
       listGet args qmk_pos qmk_A_r_a_unred
       -> whnf qmk_A_r_a_unred (mkApp qmk_A_r a)
       -> unfoldApps (mkApp qmk_A_r a) (mkConst qmk_name qmk_levels) qmk_args
       -> listGet args B_of_pos B_of
       -> listSkip args (qmk_pos + 1) skipped
       -> foldlApps (mkApp B_of a) skipped out_unred
       -> whnfCore out_unred out
       -> reduceQuotInd (mkConst qind_name c_levels) args out

with toCtorWhenK : Expr -> Declar -> Expr -> Prop
| skip (e : Expr) (d : Declar) : toCtorWhenK e d e

| base 
    (e : Expr)
    (c_name : Name)
    (d_uparams : list Level)
    (d_type : Expr)
    (d_names : list Name)
    (d_num_params : nat)
    (d_num_indices : nat)
    (d_num_motives : nat)
    (d_num_minors : nat)
    (d_major_idx : nat)
    (d_rec_rules : list RecRule)
    (d_is_unsafe : bool)
    (e_type_unred : Expr)
    (e_type : Expr)
    (c_name : Name)
    (c_levels : list Level)
    (c_args : list Expr)
    (ctor_app : Expr)
    (ctor_app_type : Expr)
    : let recursor := 
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
    -> unfoldApps e_type (mkConst c_name c_levels) c_args
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
    (major_unredA : Expr)
    (major_unredB : Expr)
    (major : Expr)
    (major_fun : Expr)
    (major_args : list Expr)
    -- rec_rule info
    (rr_ctor_name : Name)
    (rr_num_fields : nat)
    (rr_val : Expr)
    --
    (major_args_len : nat)
    (skip1 : list Expr)
    (take1 : list Expr)
    (skip2 : list Expr)
    (take2 : list Expr)
    (r12 r13 r14 r15 r16 : Expr)
    : let recursor := 
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
    -> listGet args d_major_idx major_unredA
    -> toCtorWhenK major_unredA recursor major_unredB
    -> whnf major_unredB major
    -> unfoldApps major major_fun major_args
    -> getRecRule d_rec_rules major_fun (RecRule.mk rr_ctor_name rr_num_fields rr_val)
    -> listLen major_args major_args_len
    -> listSkip major_args (major_args_len - rr_num_fields) skip1
    -> listTake skip1 rr_num_fields take1
    -> listSkip args (d_major_idx + 1) skip2
    -> listTake args (d_num_params + d_num_motives + d_num_minors) take2
    -> subst rr_val d_uparams c_levels r12
    -> foldlApps r12 take2 r13
    -> foldlApps r13 take1 r14
    -> foldlApps r14 skip2 r15
    -> whnfCore r15 r16
    -> reduceIndRec (mkConst c_name c_levels) args r16
     


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
| base (e : Expr) : whnf e (mkSort z) -> isSortZero e

with isProposition : Expr -> Expr -> Prop
| base (e inferred : Expr)
    : infer e InferOnly inferred
    -> isSortZero inferred
    -> isProposition e inferred

with isProof : Expr -> Expr -> Prop
| base (e inferred sort_of : Expr)
    : infer e InferOnly inferred
    -> isProposition inferred sort_of
    -> isProof e inferred

with proofIrrelEq : Expr -> Expr -> Prop
| base (l r : Expr)
       (l_type r_type : Expr)
    : isProof l l_type
    -> isProof r r_type
    -> defEq l_type r_type
    -> proofIrrelEq l_type r_type

with defEqSort : Expr -> Expr -> Prop
| base (l r : Level)
    : eqAntisymm l r tt
    -> defEqSort (mkSort l) (mkSort r)

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
    (serial : nat)
    : inst lt doms lt'
    -> inst rt doms rt'
    -> defEq lt' rt'
    -> defEqPi lb rb ((mkLocal ln lt' ls serial) :: doms) 
    -> defEqPi (mkPi ln lt ls lb) (mkPi rn rt rs rb) doms


with defEqLambda : Expr -> Expr -> list Expr -> Prop
| base 
    (l r : Expr)
    (doms : list Expr)
    (l' r' : Expr)
    : isLambda l ff
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
    (serial : nat)
    : inst lt doms lt'
    -> inst rt doms rt'
    -> defEq lt' rt'
    -> defEqLambda lb rb ((mkLocal ln lt' ls serial) :: doms) 
    -> defEqLambda (mkLambda ln lt ls lb) (mkLambda rn rt rs rb) doms

with argsEq : list Expr -> list Expr -> Prop
| base 
    (ls rs : list Expr)
    (shared_len : nat)
    : listLen ls shared_len
    -> listLen rs shared_len
    -> argsEqAux ls rs
    -> argsEq ls rs

with argsEqAux : list Expr -> list Expr -> Prop
| base : argsEqAux [] []
| step 
    (l_hd r_hd : Expr)
    (l_tl r_tl : list Expr)
    : defEq l_hd r_hd
    -> argsEqAux l_tl r_tl
    -> argsEqAux (l_hd :: l_tl) (r_hd :: r_tl)

with lazyDeltaStep : Expr -> Expr -> DeltaResult -> Prop
| eqSort (l r : Expr) : defEqSort l r -> lazyDeltaStep l r DeltaEq
| eqPi (l r : Expr) : defEqPi l r [] -> lazyDeltaStep l r DeltaEq
| eqLambda (l r : Expr) : defEqLambda l r [] -> lazyDeltaStep l r DeltaEq
| noneNone (l r : Expr) : lazyDeltaStep l r (Exhausted l r)
| someNone 
    (l r : Expr)
    (l_def : Declar)
    (l_defval_unred : Expr)
    (l_defval : Expr)
    (result : DeltaResult)
    : isDelta l l_def
    -> unfoldDef l l_defval_unred
    -> whnfCore l_defval_unred l_defval
    -> lazyDeltaStep l_defval r result
    -> lazyDeltaStep l r result
           
| noneSome 
    (l r : Expr)
    (r_def : Declar)
    (r_defval_unred : Expr)
    (r_defval : Expr)
    (result : DeltaResult)
    : isDelta r r_def
    -> unfoldDef r r_defval_unred
    -> whnfCore r_defval_unred r_defval
    -> lazyDeltaStep l r_defval result
    -> lazyDeltaStep l r result

| lt 
    (l r : Expr)
    (l_dname r_dname : Name)
    (l_duparams r_duparams : list Level)
    (l_dtype r_dtype : Expr)
    (l_dval r_dval : Expr)
    (l_dhint r_dhint : Hint)
    (l_dis_unsafe r_dis_unsafe : bool) 
    (r_defval_unred : Expr)
    (r_defval : Expr)
    (result : DeltaResult)
    : let l_defn := Definition l_dname l_duparams l_dtype l_dval l_dhint l_dis_unsafe,
    r_defn := Definition r_dname r_duparams r_dtype r_dval r_dhint r_dis_unsafe
    in
    isDelta l l_defn
    -> isDelta r r_defn
    -> l_dhint < r_dhint
    -> unfoldDef r r_defval_unred
    -> whnfCore r_defval_unred r_defval
    -> lazyDeltaStep l r_defval result
    -> lazyDeltaStep l r result

| gt 
    (l r : Expr)
    (l_dname r_dname : Name)
    (l_duparams r_duparams : list Level)
    (l_dtype r_dtype : Expr)
    (l_dval r_dval : Expr)
    (l_dhint r_dhint : Hint)
    (l_dis_unsafe r_dis_unsafe : bool) 
    (l_defval_unred : Expr)
    (l_defval : Expr)
    (result : DeltaResult)
    : let l_defn := Definition l_dname l_duparams l_dtype l_dval l_dhint l_dis_unsafe,
    r_defn := Definition r_dname r_duparams r_dtype r_dval r_dhint r_dis_unsafe
    in
    isDelta l l_defn
    -> isDelta r r_defn
    -> r_dhint < l_dhint
    -> unfoldDef l l_defval_unred
    -> whnfCore l_defval_unred l_defval
    -> lazyDeltaStep l l_defval result
    -> lazyDeltaStep l r result

| extensional 
    (l r : Expr)
    (shared_defn : Declar)
    (shared_cname : Name)
    (l_clevels r_clevels : list Level)
    (l_args r_args : list Expr)
    : isDelta l shared_defn
    -> isDelta r shared_defn
    -> unfoldApps l (mkConst shared_cname l_clevels) l_args
    -> unfoldApps r (mkConst shared_cname r_clevels) r_args
    -> argsEq l_args r_args
    -> eqAntisymmMany l_clevels r_clevels tt
    -> lazyDeltaStep l r DeltaEq

| eqStep 
    (l r : Expr)
    (l_dname r_dname : Name)
    (l_duparams r_duparams : list Level)
    (l_dtype r_dtype : Expr)
    (l_dval r_dval : Expr)
    (dhint : Hint)
    (l_dis_unsafe r_dis_unsafe : bool) 
    (l_defval_unred : Expr)
    (r_defval_unred : Expr)
    (l_defval : Expr)
    (r_defval : Expr)
    (result : DeltaResult)
    : let l_defn := Definition l_dname l_duparams l_dtype l_dval dhint l_dis_unsafe,
    r_defn := Definition r_dname r_duparams r_dtype r_dval dhint r_dis_unsafe
    in
    isDelta l l_defn
    -> isDelta r r_defn
    -> unfoldDef l l_defval_unred
    -> unfoldDef r r_defval_unred
    -> whnfCore l_defval_unred l_defval
    -> whnfCore r_defval_unred r_defval
    -> lazyDeltaStep r_defval l_defval result
    -> lazyDeltaStep l r result
          
with defEqConst : Expr -> Expr -> Prop
| base 
    (n : Name)
    (l_levels r_levels : list Level)
    : eqAntisymmMany l_levels r_levels tt
    -> defEqConst (mkConst n l_levels) (mkConst n r_levels)

-- Any time two Locals have the same serial, they (should be) guaranteed
-- to be identical.
with defEqLocal : Expr -> Expr -> Prop
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    : defEqLocal (mkLocal n t s serial) (mkLocal n t s serial)

with defEqApp : Expr -> Expr -> Prop
| base 
    (l r : Expr)
    (l_fun r_fun : Expr)
    (l_args r_args : list Expr)
    : unfoldApps l l_fun l_args
    -> unfoldApps r r_fun r_args
    -> defEq l_fun r_fun
    -> argsEq l_args r_args
    -> defEqApp l r

with defEqEta : Expr -> Expr -> Prop
| base 
    (r : Expr)
    (ln rn : Name)
    (lt rt : Expr)
    (ls rs : Bstyle)
    (lb rb : Expr)
    (r_type_unred : Expr)
    : infer r InferOnly r_type_unred
    -> whnf r_type_unred (mkPi rn rt rs rb)
    -> defEq (mkLambda ln lt ls lb) (mkLambda rn rt rs (mkApp r (mkVar 0)))
    -> defEqEta (mkLambda ln lt ls lb) r

with infer : Expr -> InferFlag -> Expr -> Prop
| sort 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    : inferSort e flag inferred
    -> infer e flag inferred

| const 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    : inferConst e flag inferred
    -> infer e flag inferred

| app 
    (e : Expr) 
    (flag : InferFlag)
    (f : Expr)
    (args : list Expr)
    (f_type : Expr)
    (inferred : Expr)
    : unfoldApps e f args
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
    (inferred : Expr)
    : inferLambda e [] [] flag inferred
    -> infer e flag inferred

| let_ (e : Expr)
       (flag : InferFlag)
       (inferred : Expr)
       :
       inferLet e flag inferred
       -> infer e flag inferred

| local_ 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    : inferLocal e flag inferred
    -> infer e flag inferred
      

with inferSortOf : Expr -> InferFlag -> Level -> Prop
| base 
    (e : Expr)
    (flag : InferFlag)
    (inferred : Expr)
    (l : Level)
    : infer e flag inferred
    -> whnf inferred (mkSort l)
    -> inferSortOf e flag l

with ensureSort : Expr -> Level -> Prop
| base (l : Level) : ensureSort (mkSort l) l
| step 
    (e : Expr)
    (l : Level)
    : whnf e (mkSort l)
    -> ensureSort e l

with ensureType : Expr -> Level -> Prop
| base 
    (e : Expr)
    (e_type : Expr)
    (l : Level)
    : infer e InferOnly e_type
    -> ensureSort e_type l
    -> ensureType e l

with ensurePi : Expr -> Expr -> Prop
| base (e : Expr) : isPi e tt -> ensurePi e e
| step (e e' : Expr) : whnf e e' -> isPi e' tt -> ensurePi e e'
       

with inferSort : Expr -> InferFlag -> Expr -> Prop
| inferOnly (l : Level) : inferSort (mkSort l) InferOnly (mkSort (s l))
| checked 
    (l : Level) 
    (tc_uparams : list Level)
    : paramsDefined l tc_uparams
    -> inferSort (mkSort l) Check (mkSort (s l))
            
 


with inferConst : Expr -> InferFlag -> Expr -> Prop
| inferOnly 
    (env : Env)
    (c_name : Name)
    (c_levels : list Level)
    (flag : InferFlag)
    (d : Declar)
    (d_uparams : list Level)
    (d_type : Expr)
    (inferred : Expr)
    : env.getDeclar c_name d
    /-
    -> getDeclarUparams d d_uparams
    -> getDeclarType d d_type
    -/
    -> subst d_type d_uparams c_levels inferred
    -> inferConst (mkConst c_name c_levels) InferOnly inferred

       
-- tc_uparams is the set of universe parameters from the
-- declaration currently being checked by the type checker.
| check 
    (env : Env)
    (c_name : Name)
    (c_levels : list Level)
    (flag : InferFlag)
    (tc_uparams : list Level)
    (d : Declar)
    (d_uparams : list Level)
    (d_type : Expr)
    (inferred : Expr)
    : env.getDeclar c_name d
    /-
    -> getDeclarUparams d d_uparams
    -> getDeclarType d d_type
    -/
    -> paramsDefinedMany c_levels tc_uparams
    -> subst d_type d_uparams c_levels inferred
    -> inferConst (mkConst c_name c_levels) Check inferred


with inferApp : Expr -> list Expr -> list Expr -> InferFlag -> Expr -> Prop
-- looks weird since the function body's type was inferred
-- before we star using inferApp in order to prevent the need
-- for an auxiliary function.
| base 
    (e : Expr)
    (context : list Expr)
    (flag : InferFlag)
    (inferred : Expr)
    : inst e context inferred
    -> inferApp e [] context flag inferred

| stepInferOnly 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (hd : Expr)
    (args_tl : list Expr)
    (context : list Expr)
    (inferred : Expr)
    : inferApp b args_tl (hd :: context) InferOnly inferred
    -> inferApp (mkPi n t s b) (hd :: args_tl) (context) InferOnly inferred

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
    (inferred : Expr)
    : inst t context t'
    -> infer hd Check arg_type
    -> defEq t' arg_type
    -> inferApp b args_tl (hd :: context) Check inferred
    -> inferApp (mkPi n t s b) (hd :: args_tl) (context) Check inferred

| stepNotPi 
    (e : Expr)
    (args : list Expr)
    (context : list Expr)
    (flag : InferFlag)
    (e' : Expr)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (inferred : Expr)
    : inst e context e'
    -> ensurePi e' (mkPi n t s b)
    -> inferApp (mkPi n t s b) args [] flag inferred
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
    (folded : Level)
    : isPi e ff
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
    (serial : nat)
    : inst t local_binders t'
    -> inferSortOf t' flag inferred_level
    -> inferPi b ((mkLocal n t' s serial) :: local_binders) (inferred_level :: levels) flag inferred
    -> inferPi (mkPi n t s b) local_binders levels flag inferred


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
    (folded : Expr)
    : isLambda e ff
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
    (inferred : Expr)
    (t' : Expr)
    (serial : nat)
    : inst t local_binders t'
    -> inferLambda b (t :: b_types) ((mkLocal n t' s serial) :: local_binders) InferOnly inferred
    -> inferLambda (mkLambda n t s b) b_types local_binders InferOnly inferred

       
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
    (serial : nat)
    : inst t local_binders t'
    -> inferSortOf t' Check b_type_sort
    -> inferLambda b (t :: b_types) ((mkLocal n t' s serial) :: local_binders) Check inferred
    -> inferLambda (mkLambda n t s b) b_types local_binders Check inferred


with inferLet : Expr -> InferFlag -> Expr -> Prop
| inferOnly 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (b' : Expr)
    (inferred : Expr)
    : inst1 b v b'
    -> infer b' InferOnly inferred
    -> inferLet (mkLet n t s v b) InferOnly inferred

| checked 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (t_level : Level)
    (v_type : Expr)
    (b' : Expr)
    (inferred : Expr)
    : inferSortOf t Check t_level
    -> infer v Check v_type
    -> defEq v_type t
    -> inst1 b v b'
    -> infer b' Check inferred
    -> inferLet (mkLet n t s v b) Check inferred

with inferLocal : Expr -> InferFlag -> Expr -> Prop
| base 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (flag : InferFlag)
    : inferLocal (mkLocal n t s serial) flag t
