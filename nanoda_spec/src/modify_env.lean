import 
    .name
    .level
    .expr
    .env
    .tc
    .ind
    
open Level Expr Hint Declar InferFlag


inductive calcHeightAux : ∀ (e : Expr) (base_height : nat), Prop
| var (dbj : nat) : 
    let e := mkVar dbj,
        height := 0
    in 
    calcHeightAux e height

| sort (l : Level) : 
    let e := mkSort l,
        height := 0
    in
    calcHeightAux e height

| constHit 
    (env : Env)
    (n : Name)
    (levels : list Level)
    (ups : list Level)
    (t : Expr)
    (v : Expr)
    (height : nat)
    (is_unsafe : bool) :
    let e := mkConst n levels,
        hint := Hint.Reg height,
        defn := Definition n ups t v hint is_unsafe
    in
    env.getDeclar n defn
    -> calcHeightAux e height

| constMiss (n : Name) (levels : list Level) : 
    let e := mkConst n levels,
        height := 0
    in 
    calcHeightAux e height

| app 
    (f : Expr)
    (a : Expr)
    (height1 height2 : nat) :
    let e := mkApp f a,
        height := max height1 height2
    in
    calcHeightAux f height1
    -> calcHeightAux a height2
    -> calcHeightAux e height

| pi
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (height1 height2 : nat) :
    let e := mkPi n t s b,
        height := max height1 height2
    in
    calcHeightAux t height1
    -> calcHeightAux b height2
    -> calcHeightAux e height

| lambda
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (height1 height2 : nat) :
    let e := mkLambda n t s b,
        height := max height1 height2
    in
    calcHeightAux t height1
    -> calcHeightAux b height2
    -> calcHeightAux e height

| let_
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (height1 height2 height3 : nat) :
    let e := mkLet n t s v b,
        height := max (max height1 height2) height3
    in
    calcHeightAux t height1
    -> calcHeightAux v height2
    -> calcHeightAux b height3
    -> calcHeightAux e height

-- The actual calculation for height finds the height of 
-- the highest term in the definition's body, and then adds 1.
def calcHeight (e : Expr) (height : nat) : Prop := calcHeightAux e (nat.pred height)

inductive checkVitals (n : Name) (ups : list Level) (t : Expr) : Prop
| base (inferred : Expr) (sort_of : Level) :
    listNoDupes ups
    -> infer t Check inferred
    -> ensureSort inferred sort_of
    -> checkVitals



/-
checking/adding unsafe definitions is more or less the same as the 
procedure for safe definitions, the difference is that the definition 
is added to the environment after `checkVitals` and before
inferring the value's type. Since (as things are now) we're assuming 
the verifier is using the environment in a linear manner, and we're 
therefore not indexing step relations by the environment, we leave
enforcement of that ordering up to the verifier.
-/



/-
for ALL of these, there's an assertion that the environment never
contains duplicate name keys. Explicitly logging a proof of this every time
we add an item to the environment would be really wasteful, so it's left 
to the verifier.

The `env` will be a pointer to the last AdmitDeclar
step, and `env'` can be interpreted as the step number for the
addition of the declaration to the environment, which is what
the next addition will reference as its initial `env`.
-/

inductive declareAxiom (env : Env) : ∀ (d : Declar) (env' : Env), Prop
| base 
    (n : Name)
    (t : Expr)
    (ups : list Level)
    (is_unsafe : bool) :
    let ax := Axiom n ups t is_unsafe,
        -- env' is the leading number of the AddDeclar step in the output.
        env' := ax.asKvPair :: env
    in
    -- ASSERT : n ∉ env.keys
    checkVitals n ups t
    -> declareAxiom ax env'

inductive declareQuot (env : Env) : ∀ (d : Declar) (env' : Env), Prop
| base 
    (n : Name)
    (ups : list Level)
    (t : Expr)
    (env : Env) :
    let q := Quot n ups t,
        -- env' is the leading number of the AddDeclar step in the output.
        env' := q.asKvPair :: env
    in 
    -- ASSERT : n ∉ env.keys
    declareQuot q env'

inductive declareSafeDef (env : Env) : ∀ (d : Declar) (env' : Env), Prop
| base
    (env' : Env) 
    (n : Name)
    (ups : list Level)
    (t : Expr)
    (v : Expr)
    (hint : Hint) 
    (inferred : Expr) :
    let
        is_unsafe := tt,
        defn := Definition n ups t v hint is_unsafe,
    -- env' will be the leading 'step' number for the `AdmitDeclar` step.
        env' := defn.asKvPair :: env
    in
    -- ASSERT : n ∉ env.keys
    checkVitals n ups t
    -> infer v Check inferred
    -> defEq t inferred
    -> declareSafeDef defn env'

inductive declareIndTypes 
    (env : Env)
    (indblock : Indblock)
    (ds : list Declar) :
    ∀ (indblock' : CheckedIndblock)
      (env' : Env),
      Prop
| base 
    (local_params : list Expr)
    (local_indices : list Expr)
    (ind_consts : list Expr)
    (codom_level : Level)
    (is_zero : bool)
    (is_nonzero : bool) :
    let 
        indblock' : CheckedIndblock := {
            codom_level := codom_level,
            is_zero := is_zero,
            is_nonzero := is_nonzero,
            params := local_params,
            indices := local_indices,
            ind_consts := ind_consts,
            ..indblock
        },
    -- env' will be the leading 'step' number for the `AdmitDeclar` step.
        env' := ds.map asKvPair ++ env
    in
    -- ASSERT : ∀ n, n ∈ indblock.ind_names → n ∉ env.keys
    checkIndTypes indblock local_params local_indices codom_level ind_consts
    -> isZero codom_level is_zero
    -> isNonzero codom_level is_nonzero
    -> mkIndTypes indblock indblock.ind_names indblock.ind_types indblock.ctor_names ds
    -> declareIndTypes indblock' env'



/-
Once all of the constructors in the block are made/checked
we add them to the environment.
-/
inductive declareCtors 
    (env : Env)
    (indblock : CheckedIndblock)
    (ctors : list Declar) :
    ∀ (env' : Env),
      Prop
| base :
    -- env' will be the leading 'step' number for the `AdmitDeclar` step.
  let env' := (ctors.map asKvPair) ++ env
  in
  -- ASSERT : ∀ n, n ∈ indblock.ctor_names → n ∉ env.keys
  mkCtors 
    indblock 
    indblock.ind_names 
    indblock.ind_types 
    indblock.ind_consts 
    indblock.ctor_names 
    indblock.ctor_types
    ctors
  -> declareCtors env'

inductive declareRecursors
    (env : Env)
    (indblock : CheckedIndblock)
    (recursors : list Declar) :
    ∀ (env' : Env),
      Prop
| base 
    (majors : list Expr)
    (motives : list Expr)
    (minors : list Expr)
    (indices : list Expr)
    (elim_level : Level)
    (k_target : bool)
    (rec_rules : list RecRule) :
    -- env' will be the leading 'step' number for the `AdmitDeclar` step.
    let env' := recursors.map asKvPair ++ env
    in
    -- ASSERT : ∀ n, n ∈ recursors.names → n ∉ env.keys
    mkElimLevel indblock elim_level
    -> initKTarget indblock k_target
    -> mkMajors indblock indblock.params indblock.indices indblock.ind_consts majors
    -> mkMotives elim_level majors indblock.indices motives
    -> mkMinors indblock motives minors
    -> mkRecRules indblock motives indblock.ind_names indblock.ind_types indblock.ind_consts indblock.ctor_names indblock.ctor_types minors rec_rules
    -> mkRecursors indblock motives k_target elim_level indblock.ind_names motives majors indblock.indices minors rec_rules recursors
    -> declareRecursors env'

    



