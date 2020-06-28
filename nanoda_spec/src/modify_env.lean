import 
    .name
    .level
    .expr
    .env
    .tc
    .ind
    
open Expr Declar InferFlag

inductive calcHeightAux : Expr -> nat -> Prop
| cacheHit 
    (e : Expr)
    (height : nat)
    : calcHeightAux e height -> calcHeightAux e height

| var (dbj : nat) : calcHeightAux (mkVar dbj) 0

| sort (l : Level) : calcHeightAux (mkSort l) 0

| constHit 
    (env : Env)
    (n : Name)
    (levels : list Level)
    (ups : list Level)
    (t : Expr)
    (v : Expr)
    (height : nat)
    (is_unsafe : bool)
    : env.getDeclar n (Definition n ups t v (Hint.Reg height) is_unsafe)
      -> calcHeightAux (mkConst n levels) height

| constMiss (n : Name) (levels : list Level) : calcHeightAux (mkConst n levels) 0

| app 
    (f : Expr)
    (a : Expr)
    (height1 height2 : nat)
    : calcHeightAux f height1
    -> calcHeightAux a height2
    -> calcHeightAux (mkApp f a) (max height1 height2)

| pi
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (height1 height2 : nat)
    : calcHeightAux t height1
    -> calcHeightAux b height2
    -> calcHeightAux (mkPi n t s b) (max height1 height2)

| lambda
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (height1 height2 : nat)
    : calcHeightAux t height1
    -> calcHeightAux b height2
    -> calcHeightAux (mkLambda n t s b) (max height1 height2)

| let_
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr)
    (height1 height2 height3 : nat)
    : calcHeightAux t height1
    -> calcHeightAux v height2
    -> calcHeightAux b height3
    -> calcHeightAux (mkLet n t s v b) (max height1 (max height2 height3))

def calcHeight (e : Expr) (height : nat) : Prop := calcHeightAux e (nat.pred height)

inductive checkVitals : Name -> list Level -> Expr -> Prop
| base 
    (n : Name)
    (ups : list Level)
    (t : Expr)
    (inferred : Expr)
    (sort_of : Level)
    : listNoDupes ups
    -> infer t Check inferred
    -> ensureSort inferred sort_of
    -> checkVitals n ups t 

-- Unfortunately check and admit despite being nice 
-- starting places are the things that are going to fall
-- into place until I get the inductive/field thing
-- sorted out, so checkOk and admitDeclar don't
-- perfectly match up with the Rust steps right now.
/-
Two notes about definitions:
1.
checking/adding unsafe definitions is more or less the same as the 
procedure for safe definitions, the difference is that the definition 
is added to the environment after `checkVitals` and before
inferring the value's type. Since (as things are now) we're assuming 
the verifier is using the environment in a linear manner, and we're 
therefore not indexing step relations by the environment, we leave
enforcement of that ordering up to the verifier.

2.
I'm not sure what the rules are in lean 4 export files will be 
w.r.t when a definition is supposed to have Opaque/Abbrev 
reducibility hints, so right now we're just using the lean 3 
convention that all definitions have `Reg n` reducibility 
hints indicating their height.
-/

inductive checkOk : Declar -> Prop
| ax 
    (n : Name)
    (ups : list Level)
    (t : Expr)
    (is_unsafe : bool)
    : checkVitals n ups t 
    -> checkOk (Axiom n ups t is_unsafe)

-- see above comment about unsafe Definitions
| defn
  (n : Name)
  (ups : list Level)
  (t : Expr)
  (v : Expr)
  (height : nat)
  (is_unsafe : bool)
  (inferred : Expr)
  : let d := Definition n ups t v (Hint.Reg height) is_unsafe
  in calcHeight v height
  -> checkVitals n ups t
  -> infer v Check inferred
  -> defEq t inferred
  -> checkOk d

| quot
  (env : Env)
  (n : Name)
  (ups : list Level)
  (t : Expr)
  : checkOk (Quot n ups t)


| ind
  (env : Env)
  (n : Name)
  (ups : list Level)
  (t : Expr)
  (num_params : nat)
  (all_ind_names : list Name)
  (all_ctor_names : list Name)
  (is_unsafe : bool) 
  : let d := Inductive n ups t num_params all_ind_names all_ctor_names is_unsafe
  in checkIndType t
  -> checkOk d

| ctor
  (env : Env)
  (n : Name)
  (ups : list Level)
  (t : Expr)
  (parent_name : Name)
  (num_fields : nat)
  (minor_idx : nat)
  (num_params : nat)
  (is_unsafe : bool)  
  : let d := Constructor n ups t parent_name num_fields minor_idx num_params is_unsafe
  in checkIndType t
  -> checkOk d

| recursor
  (env : Env)
  (n : Name)
  (ups : list Level)
  (t : Expr)
  (all_names : list Name)
  (num_params : nat)
  (num_indices : nat)
  (num_motives : nat)
  (num_minors : nat)
  (major_idx : nat)
  (rec_rules : list RecRule)
  (is_k : bool)
  (is_unsafe : bool)  
  : let d := Recursor 
      n 
      ups 
      t 
      all_names 
      num_params 
      num_indices 
      num_motives 
      num_minors 
      major_idx 
      rec_rules 
      is_k 
      is_unsafe
  in checkOk d


inductive admitDeclar : Env -> Declar -> Prop
| mk 
    (env : Env) 
    (n : Name) 
    (d : Declar) 
    : getDeclarName d n 
    -> checkOk d 
    -> admitDeclar ((n, d) :: env) d

axiom mem_iff_admitted (n : Name) (d : Declar) (env : Env) (h : getDeclarName d n) : admitDeclar env d ↔ (n, d) ∈ env