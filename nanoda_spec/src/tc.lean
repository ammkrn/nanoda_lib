import .name 
       .level 
       .expr
       .env

open Level Expr Declar

inductive InferFlag 
| Check
| InferOnly

instance : decidable_eq InferFlag := by tactic.mk_dec_eq_instance

open InferFlag



inductive whnfSort : Expr -> Expr -> Prop
| mk (l l' : Level) : simplify l l' -> whnfSort (mkSort l) (mkSort l')

-- whnfLambda requires that the caller then call `whnf_core` on the result
-- to finish reduction. We don't include the call here to avoid the
-- need for a mutually inductive prop (whnf/whnflambda)
-- in the neither case (not a lambda and no args) you do `baseNoArgs`.
inductive whnfLambda : Expr -> list Expr -> list Expr -> Expr -> Prop
| baseNotLambda (e : Expr) 
                (rem_args lambda_args : list Expr) 
                (e' e'' : Expr) 
                : isLambda e ff
                  -> inst e lambda_args e'
                  -> foldlApps e' rem_args e''
                  -> whnfLambda e rem_args lambda_args e''

| baseNoArgs  (e : Expr) 
              (lambda_args : list Expr) 
              (e' : Expr) 
              : inst e lambda_args e'
                -> whnfLambda e [] lambda_args e'

| step (b_name : Name)
       (b_type : Expr)
       (b_style : Bstyle)
       (body : Expr)
       (hd_arg : Expr)
       (tl_rem_args : list Expr)
       (tl_lambda_args : list Expr)
       (e' : Expr)
       : whnfLambda body tl_rem_args (hd_arg :: tl_lambda_args) e'
         -> whnfLambda (mkLambda b_name b_type b_style body) 
                       (hd_arg :: tl_rem_args) 
                       (tl_lambda_args) 
                       e'
                  
-- Requires that caller use whnf_core again on the produced result
inductive whnfLet : Expr -> Expr -> Prop
| mk (b_name : Name)
     (b_type : Expr)
     (b_style : Bstyle)
     (val : Expr)
     (body : Expr)
     (body' : Expr)
     : inst body [val] body'
       -> whnfLet (mkLet b_name b_type b_style val body) body'

inductive whnfCore : Expr -> Expr -> Prop
| sort (e : Expr) 
       (l : Level) 
       (e' : Expr) 
       : unfoldApps e (mkSort l) []
         -> whnfSort (mkSort l) e'
         -> whnfCore e e'

| lambda (e lam : Expr) 
         (all_args : list Expr) 
         (e' e'' : Expr) 
         : unfoldApps e lam all_args
           -> whnfLambda lam all_args [] e'
           -> whnfCore e' e''
           -> whnfCore e e''

| letE (e0 : Expr)
       (let_ : Expr)
       (args : list Expr)
       (e1 : Expr)
       (e2 : Expr)
       (e3 : Expr)
       : unfoldApps e0 let_ args
         -> whnfLet let_ e1
         -> foldlApps e1 args e2
         -> whnfCore e2 e3
         -> whnfCore e0 e3

/-
--inductive whnf : Expr → Expr → Prop
--
--inductive whnfCore : Expr → Expr → Prop
--| mkSort (l l' : Level) : unfoldApps simplify l l' → whnfCore (sort l) (sort l')
--| mkLambda
--| mkLet
--| quotLift
--| quotInd
--| indRec
--| owise

/-
The check of whether or not (infer arg) =?= b_type isn't done here.
-/

-- This is the big-step version.
inductive infer (dec_ups : option $ list Level) (flag : InferFlag) : Expr → Expr → Prop
--| baseLambda (b_names  : list Name)
--             (b_types  : list Expr)
--             (b_styles : list Bstyle)
--             (locals : list Expr)
--             (body instd infd abstrd : Expr) : inst body locals body'
--
--| stepLambda (b_type b_type' body body' : Expr)
--             (b_name : Name)
--             (b_style : Bstyle)
--             (serial : nat)
--             (flag : InferFlag)
--inductive inferChecked (dec_ups : list Level) : Expr → Expr → Prop
--| baseSort (l : Level) : allParamsDefined l dec_ups → inferChecked (mkSort l) (mkSort $ s l)
--| baseConst (n : Name) 
--            (levels : list Level) 
--            (env : Env) 
--            (d_name : Name)
--            (d_ups : list Level)
--            (d_type d_type' : Expr)
--            (d : Declar) : 
--            (d_name, d) ∈ env
--            → allParamsDefinedMany levels dec_ups
--            → declarVitals d d_name d_ups d_type
--            → subst d_ups levels d_type d_type'
--            → inferChecked (mkConst n levels) (d_type')
--            
--| baseLocal (b_name : Name) (b_type : Expr) (b_style : Bstyle) (serial : nat) : infer (mkLocal b_name b_type b_style serial) b_type


inductive lazyDelta : Expr → Expr → Prop


inductive isSortZero : Expr → Prop
| base (e : Expr) : whnf e (mkSort z) → isSortZero e

inductive isProposition (dec_ups : option $ list Level) : Expr → Prop
| base (e infd : Expr) : infer dec_ups InferOnly e infd 
                         → isSortZero infd 
                         → isProposition e

-- Is this a value, whose type infers as some proposition P, where P will then necessarily infer as Sort 0
inductive isProof (dec_ups : option $ list Level) : Expr → Expr → Prop
| base (e infd : Expr) : infer dec_ups InferOnly e infd 
                         → isProposition dec_ups infd 
                         → isProof e infd




/-
The defEq constructors end up requiring more introductory evidnce about reduction (whnf → lazyDelta → ...)
in the interest of making the spec and export file format to dovetail as nicely as possible, since the
export file's shape is directly related to the control flow in the source code.
IE we know that any time we actually use the defEq.eqApps constructor, we've already reduced both sides
using whnfCore and then lazyDelta.

It's true that it would be more general to have like a transitive relation that says 
essentially "if there's a sequence of reduction steps bringing e1 to e1', and e1' is defEq to e2, then e1
is defEq to e2", but getting that to show up correctly in the export file in a way that mm0 can understand it
without doing extra work would require making changes to the source code. While I'm not generally opposed to doing that,
the order of reduction steps taken in in the CPP code base (and also Nanoda) is the most efficient order,
so we're just going to run with it.

Outside of the sequence, (whnfCore → lazyDelta → ...) there's not a whole lot that can be done anyway.
You want to avoid using the unfolding/full version of `whnf` outside of specific places, since unfolding
in the wrong place can be wildly expensive.
-/

inductive defEq (dec_ups : option $ list Level) : Expr → Expr → Prop
| byRefl (e : Expr) : defEq e e
| cacheHit (e1 e2 : Expr) : defEq e1 e2 → defEq e1 e2
| eqSort (e1 e2 : Expr) 
         (l1 l2 : Level) : whnfCore e1 (mkSort l1)
                           → whnfCore e2 (mkSort l2)
                           → eqAntisymm l1 l2 
                           → defEq e1 e2

| eqPi (n1 n2 : Name)
       (t1 t2 body1 body1' body2 body2' : Expr)
       (s1 s2 : Bstyle)
       (e1 e2 : Expr)
       (serial : ℕ) :
           let local1 : Expr := mkLocal n1 t1 s1 serial
           in  
           whnfCore e1 (mkPi n1 t1 s1 body1)
              → whnfCore e2 (mkPi n2 t2 s2 body2)
              → defEq t1 t2        
              → inst1 body1 local1 body1'
              → inst1 body2 local1 body2'
              → defEq body1' body2'
              → defEq e1 e2

| eqLambda (b_name1 b_name2 : Name)
           (b_type1 b_type2 body1 body1' body2 body2' : Expr)
           (b_style1 b_style2 : Bstyle)
           (e1 e2 : Expr)
           (serial : ℕ) :
               let local1 : Expr := mkLocal b_name1 b_type1 b_style1 serial
               in  
               whnfCore e1 (mkLambda b_name1 b_type1 b_style1 body1)
                  → whnfCore e2 (mkLambda b_name2 b_type2 b_style2 body2)
                  → defEq b_type1 b_type2        
                  → inst1 body1 local1 body1'
                  → inst1 body2 local1 body2'
                  → defEq body1' body2'
                  → defEq e1 e2            

| proofIrrel (e1 e2 e1' e2' some_prop : Expr) : whnfCore e1 e1'
                                        → whnfCore e2 e2'
                                        → isProof dec_ups e1' some_prop
                                        → isProof dec_ups e2' some_prop
                                        --→ infer e1' some_prop 
                                        --→ infer e2' some_prop 
                                        → defEq e1 e2

| eqConst (e1 e1' e2 e2' : Expr)
          (n : Name) 
          (ls1 ls2 : list Level) : whnfCore e1 e1'
                                   → whnfCore e2 e2'
                                   → lazyDelta e1' (mkConst n ls1)
                                   → lazyDelta e2' (mkConst n ls2)
                                   → eqAntisymmList ls1 ls2 
                                   → defEq (mkConst n1 ls1) (mkConst n2 ls2)

-- The proof obgligation is just that the serials are the same
| eqLocal (b_name : Name)
          (e1 e2 e1' e2' b_type : Expr)
          (b_style  : Bstyle)
          (serial : ℕ) : 
          let sharedLocal := (mkLocal b_name b_type b_style serial) 
          in whnfCore e1 e1'
             → whnfCore e2 e2'
             → lazyDelta e1' sharedLocal
             → lazyDelta e2' sharedLocal
             → defEq e1 e2

| eqApp (e1 e1' e2 e2' f1 f2 a1 a2 : Expr) : whnfCore e1 e1'
                                             → whnfCore e2 e2'
                                             → lazyDelta e1' (mkApp f1 a1)
                                             → lazyDelta e2' (mkApp f2 a2)
                                             → defEq f1 f2
                                             → defEq a1 a2 
                                             → defEq e1 e2


| etaRight (L L' R R' R'' R_T b_type1 b_type2 body1 body2 : Expr)
          (b_name1 b_name2 : Name)
          (b_style1 b_style2 : Bstyle) : 
              whnfCore L L'
              → whnfCore R R'
              → lazyDelta L' (mkLambda b_name1 b_type1 b_style1 body1)
              → lazyDelta R' R''
              -- Where we actually enter the function try_eta_expand
              → notLambda R''
              → infer dec_ups InferOnly R'' R_T
              → whnf R_T (mkPi b_name2 b_type2 b_style2 body2)
              → defEq (mkLambda b_name1 b_type1 b_style1 body1) (mkLambda b_name2 b_type2 b_style2 (mkApp R'' (mkVar 0)))
              → defEq L R



--inductive infer (dec_ups : list Level) : Expr → Expr → Prop

inductive ensureSort (dec_ups : option $ list Level) : Expr → Level →  Prop
| base (l : Level) : ensureSort (sort l) l
| whnfStep (e e' : Expr) (l : Level) : whnf /-dec_ups-/ e (sort l)
                                       → ensureSort e l

-- technically relies on not being called with a value that's in Prop
inductive ensureType (dec_ups : option $ list Level) : Expr → Level → Prop
| base (e e' : Expr) (l : Level) : infer dec_ups InferOnly e e'
                                   → ensureSort dec_ups e' l
                                   → ensureType e l
                                   -/
                            
