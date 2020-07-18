import .name
import .level
import .utils

open nat Name Level


/-
Binder style. Although this is never used at any point to directly determine 
control flow in the type checker (IE we never say "If this is an implicit, do this, else do that...")
it can still indirectly affect control flow since it can cause us to miss
on reflexive/structural equality when checking for definitional equality.
We'll still catch the equality elsewhere, but the actual proof of their
equality will be different
-/

inductive Bstyle
| Default
| Implicit
| StrictImplicit
| InstImplicit

instance : decidable_eq Bstyle := by tactic.mk_dec_eq_instance

/-
`let` and `local` are reserved keywords in Lean. 
Escaping literals with « » is very frustrating, so let
and local are just renamed to letE and localE respectively.
-/
inductive Expr
| var (dbj : nat) : Expr
| sort (level : Level) : Expr
| const (name : Name) (levels : list Level) : Expr

| app 
    (f : Expr) 
    (a : Expr)
    (var_bound : nat)
    (has_locals : bool) 
    : Expr

| pi  
    (n : Name) 
    (t : Expr) 
    (s : Bstyle) 
    (body : Expr)
    (var_bound : nat)
    (has_locals : bool) 
    : Expr
      
| lambda 
    (n : Name) 
    (t : Expr) 
    (s : Bstyle) 
    (body : Expr)
    (var_bound : nat)
    (has_locals : bool) 
    : Expr

| letE 
    (n : Name) 
    (t : Expr) 
    (s : Bstyle) 
    (val : Expr)
    (body : Expr)
    (var_bound : nat)
    (has_locals : bool) 
    : Expr

| localE 
    (n : Name) 
    (t : Expr) 
    (s : Bstyle) 
    (serial : nat) 
    : Expr


instance : decidable_eq Expr := by tactic.mk_dec_eq_instance

namespace Expr

def var_bound : Expr -> nat 
| (var dbj) := dbj + 1
| (sort _) := 0
| (const _ _) := 0
| (app _ _ vb _) := vb
| (pi _ _ _ _ vb _) := vb
| (lambda _ _ _ _ vb _) := vb
| (letE _ _ _ _ _ vb _) := vb
| (localE _ _ _ _) := 0

def has_locals : Expr -> bool
| (var dbj) := false
| (sort _) := false
| (const _ _) := false
| (app _ _ _ ls) := ls
| (pi _ _ _ _  _ ls) := ls
| (lambda _ _ _ _ _ ls) := ls
| (letE _ _ _ _ _ _ ls) := ls
| (localE _ _ _ _) := true

def mkVar (dbj : nat) : Expr := var dbj

def mkSort (level : Level) : Expr := sort level

def mkConst (name : Name) (levels : list Level) : Expr := const name levels

def mkApp (f a: Expr) : Expr :=
    let bound : nat := max (var_bound f) (var_bound a),
    locals : bool := has_locals f || has_locals a
    in app f a bound locals

def mkPi (n : Name) (t : Expr) (s : Bstyle) (b : Expr) : Expr :=
    let bound := max (t.var_bound) (pred b.var_bound),
    locals := t.has_locals || b.has_locals
    in pi n t s b bound locals

def mkLambda (n : Name) (t : Expr) (s : Bstyle) (b : Expr) : Expr:=
    let bound := max (t.var_bound) (pred b.var_bound),
    locals := t.has_locals || b.has_locals
    in lambda n t s b bound locals

def mkLet (n : Name) (t : Expr) (s : Bstyle) (v : Expr) (b : Expr) : Expr :=
    let bound := max (max (var_bound t) (var_bound v)) (pred b.var_bound),
    locals := has_locals t || has_locals v || has_locals b
    in letE n t s v b bound locals

def mkLocal (n : Name) (t : Expr) (s : Bstyle) (serial : nat) : Expr :=
    localE n t s serial

-- Tracking/managing this is up to the implementation.
inductive nextSerial : nat -> Prop
            
inductive isApp : Expr -> bool -> Prop
| var (dbj : nat) : isApp (mkVar dbj) ff
| sort (l : Level) : isApp (mkSort l) ff
| const (n : Name) (ls : list Level) : isApp (mkConst n ls) ff
| app (f a : Expr) : isApp (mkApp f a) tt
| pi (n : Name) (t body : Expr) (s : Bstyle) : isApp (mkPi n t s body) ff
| lambda (n : Name) (t body : Expr) (s : Bstyle) : isApp (mkLambda n t s body) ff
| letE (n : Name) (t val body : Expr) (s : Bstyle) : isApp (mkLet n t s val body) ff
| localE (n : Name) (t : Expr) (s : Bstyle) (serial : nat) : isApp (mkLocal n t s serial) ff


inductive isPi : Expr -> bool -> Prop
| var (dbj : nat) : isPi (mkVar dbj) ff
| sort (l : Level) : isPi (mkSort l) ff
| const (n : Name) (ls : list Level) : isPi (mkConst n ls) ff
| app (f a : Expr) : isPi (mkApp f a) ff
| pi (n : Name) (t body : Expr) (s : Bstyle) : isPi (mkPi n t s body) tt
| lambda (n : Name) (t body : Expr) (s : Bstyle) : isPi (mkLambda n t s body) ff
| letE (n : Name) (t val body : Expr) (s : Bstyle) : isPi (mkLet n t s val body) ff
| localE (n : Name) (t : Expr) (s : Bstyle) (serial : nat) : isPi (mkLocal n t s serial) ff


inductive isLambda : Expr -> bool -> Prop
| var (dbj : nat) : isLambda (mkVar dbj) ff
| sort (l : Level) : isLambda (mkSort l) ff
| const (n : Name) (ls : list Level) : isLambda (mkConst n ls) ff
| app (f a : Expr) : isLambda (mkApp f a) ff
| pi (n : Name) (t body : Expr) (s : Bstyle) : isLambda (mkPi n t s body) ff
| lambda (n : Name) (t body : Expr) (s : Bstyle) : isLambda (mkLambda n t s body) tt
| letE (n : Name) (t val body : Expr) (s : Bstyle) : isLambda (mkLet n t s val body) ff
| localE (n : Name) (t : Expr) (s : Bstyle) (serial : nat) : isLambda (mkLocal n t s serial) ff


inductive instAux : 
    ∀ (e : Expr) 
      (subs : list Expr) 
      (offset : nat) 
      (e' : Expr), 
      Prop
     
| noBound 
    (e : Expr)
    (subs : list Expr)
    (offset : nat) :
    -- ASSERT : var_bound e ≤ offset
    var_bound e ≤ offset 
    -> instAux e subs offset e

| varHit 
    (dbj : nat)
    (subs : list Expr)
    (offset : nat) :
    let e := mkVar dbj,
        e' := getInfal subs (dbj - offset)
    in
    instAux e subs offset e'

| varMiss 
    (dbj : nat)
    (subs : list Expr)
    (offset : nat) :
    let e := mkVar dbj
    in
    -- ASSERT : subs.nth (dbj - offset) = none
    instAux e subs offset e

| app 
    (f : Expr)
    (a : Expr) 
    (subs : list Expr)
    (offset : nat) 
    (f' : Expr)
    (a' : Expr) :
    let e := mkApp f a,
        e' := mkApp f' a'
    in
    instAux f subs offset f'
    -> instAux a subs offset a'
    -> instAux e subs offset e'
                       
| pi 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' : Expr)
    (body' : Expr) :
    let e := mkPi n t s body,
        e' := mkPi n t' s body'
    in
    instAux t subs offset t'
    -> instAux body subs (1 + offset) body'
    -> instAux e subs offset e'

| lambda 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' : Expr)
    (body' : Expr) :
    let e := mkLambda n t s body,
        e' := mkLambda n t' s body'
    in
    instAux t subs offset t'
    -> instAux body subs (1 + offset) body'
    -> instAux e subs offset e'

| letE 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (val : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' : Expr)
    (val' : Expr)
    (body' : Expr) :
    let e := mkLet n t s val body,
        e' := mkLet n t' s val' body'
    in
    instAux t subs offset t'
    -> instAux val subs offset val'
    -> instAux body subs (1 + offset) body'
    -> instAux e subs offset e'

inductive inst : ∀ (e : Expr) (subs : list Expr) (e' : Expr), Prop 
| noBound (e : Expr) (subs : list Expr) (e' : Expr) : var_bound e = 0 -> inst e subs e
| byAux (e : Expr) (subs : list Expr) (e' : Expr) : instAux e subs 0 e' -> inst e subs e'

def inst1 (e sub e' : Expr) : Prop := inst e [sub] e'


inductive abstrAux : ∀ (e : Expr) (locals : list Expr) (offset : nat) (e' : Expr), Prop
| noLocals 
    (e : Expr)
    (locals : list Expr)
    (offset : nat) :
    has_locals e = false
    -> abstrAux e locals offset e
           
| localHit 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (locals : list Expr)
    (offset : nat)
    (pos : nat) :
    let e := mkLocal n t s serial,
        e' := mkVar (offset + pos)
    in 
    listPos e locals (some pos)
    -> abstrAux e locals offset e'

| localMiss 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (locals : list Expr)
    (offset : nat) :
    let e := mkLocal n t s serial
    in 
    listPos e locals none
    -> abstrAux e locals offset e

| app 
    (f : Expr) 
    (a : Expr) 
    (locals : list Expr)
    (offset : nat) 
    (f' : Expr)
    (a' : Expr) :
    let e := mkApp f a,
        e' := mkApp f' a'
    in
    abstrAux f locals offset f'
    -> abstrAux a locals offset a'
    -> abstrAux e locals offset e'

| pi 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' : Expr)
    (body' : Expr) :
    let e := mkPi n t s body,
        e' := mkPi n t' s body'
    in
    abstrAux t locals offset t'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux e locals offset e'

| lambda 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' : Expr)
    (body' : Expr) :
    let e := mkLambda n t s body,
        e' := mkLambda n t' s body'
    in
    abstrAux t locals offset t'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux e locals offset e'

| letE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (val : Expr)
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' : Expr)
    (val' : Expr)
    (body' : Expr) :
    let e := mkLet n t s val body,
        e' := mkLet n t' s val' body'
    in 
    abstrAux t locals offset t'
    -> abstrAux val locals offset val'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux e locals offset e'

  
  
  
inductive abstr : ∀ (e : Expr) (locals : list Expr) (e' : Expr), Prop
| noLocals (e : Expr) (locals : list Expr) : has_locals e = false -> abstr e locals e
| byAux 
    (e : Expr) 
    (locals : list Expr) 
    (e' : Expr) 
    : abstrAux e locals 0 e'
    -> abstr e locals e'


-- "beta" substitution for levels in an expression (Sort/Const exprs)
inductive subst : ∀ (e : Expr) (ks : list Level) (vs : list Level) (e' : Expr), Prop

| var 
    (dbj : nat) 
    (ks : list Level)
    (vs : list Level) :
    let e := mkVar dbj
    in
    subst e ks vs e

| sort 
    (l : Level) 
    (ks : list Level) 
    (vs : list Level) 
    (l' : Level) :
    let e := mkSort l,
        e' := mkSort l'
    in
    l.subst ks vs l'
    -> subst e ks vs e'

| const 
    (n : Name) 
    (levels : list Level)
    (ks : list Level)
    (vs : list Level)
    (levels' : list Level) :
    let e := mkConst n levels,
        e' := mkConst n levels'
    in
    Level.substMany ks vs levels levels'                                                 
    -> subst e ks vs e'

| app 
    (f : Expr) 
    (a : Expr) 
    (ks : list Level)
    (vs : list Level)
    (f' : Expr)
    (a' : Expr) :
    let e := mkApp f a,
        e' := mkApp f' a'
    in
    subst f ks vs f' 
    -> subst a ks vs a' 
    -> subst e ks vs e'

| pi 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (ks : list Level)
    (vs : list Level)
    (t' : Expr)
    (body' : Expr) :
    let e := mkPi n t s body,
        e' := mkPi n t' s body'
    in
    subst t ks vs t' 
    -> subst body ks vs body'
    -> subst e ks vs e'

| lambda 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (ks : list Level)
    (vs : list Level)
    (t' : Expr)
    (body' : Expr) :
    let e := mkLambda n t s body,
        e' := mkLambda n t' s body'
    in
    subst t ks vs t' 
    -> subst body ks vs body'
    -> subst e ks vs e'

| letE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (val : Expr)
    (body : Expr)
    (ks vs : list Level)
    (t' : Expr)
    (val' : Expr)
    (body' : Expr) :
    let e := (mkLet n t s val body),
        e' := (mkLet n t' s val' body') 
    in
    subst t ks vs t' 
    -> subst val ks vs val'
    -> subst body ks vs body'
    -> subst e ks vs e'           

| localE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat) 
    (ks : list Level)
    (vs : list Level)
    (t' : Expr)
    (serial' : nat) :
    let e := mkLocal n t s serial,
        e' := mkLocal n t' s serial'
    in
    subst t ks vs t' 
    -> subst e ks vs e'



inductive hasIndOcc : ∀ (e : Expr) (names : list Name) (has_ind_occ : bool), Prop
| var 
    (dbj : nat) 
    (ind_names : list Name) : 
    let e := mkVar dbj,
        result := ff
    in
    hasIndOcc e ind_names result
    
| sort 
    (l : Level) 
    (ind_names : list Name) : 
    let e := mkSort l,
        result := ff
    in
    hasIndOcc e ind_names result

| const 
    (n : Name)
    (levels : list Level)
    (ind_names : list Name)
    (maybe_pos : option nat) :
    let e := mkConst n levels,
        result := maybe_pos.is_some
    in
    listPos n ind_names maybe_pos
    -> hasIndOcc e ind_names result

| app 
    (f : Expr)
    (a : Expr)
    (ind_names : list Name)
    (b1 : bool) 
    (b2 : bool) :
    let e := mkApp f a,
        result := b1 || b2
    in
    hasIndOcc f ind_names b1
    -> hasIndOcc a ind_names b2
    -> hasIndOcc e ind_names result

| pi 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (body : Expr)
    (b1 : bool) 
    (b2 : bool) 
    (ind_names : list Name) :
    let e := mkPi n t s body,
        result := b1 || b2
    in
    hasIndOcc t ind_names b1
    -> hasIndOcc body ind_names b2
    -> hasIndOcc e ind_names result

| lambda 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (body : Expr)
    (b1 : bool) 
    (b2 : bool) 
    (ind_names : list Name) :
    let e := mkLambda n t s body,
        result := b1 || b2
    in
    hasIndOcc t ind_names b1
    -> hasIndOcc body ind_names b2
    -> hasIndOcc e ind_names result
                            
| letE   
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (val : Expr)
    (body : Expr)
    (b1 : bool) 
    (b2 : bool)
    (b3 : bool)
    (ind_names : list Name) :
    let e := mkLet n t s val body,
        result := b1 || b2 || b3
    in
    hasIndOcc t ind_names b1
    -> hasIndOcc val ind_names b2
    -> hasIndOcc body ind_names b3
    -> hasIndOcc e ind_names result
                            
| localE 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (b : bool) 
    (ind_names : list Name) :
    let e := mkLocal n t s serial
    in
    hasIndOcc t ind_names b
    -> hasIndOcc e ind_names b



inductive applyPi : ∀ (binder body out : Expr), Prop
| mk 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (body : Expr)
    (body' : Expr) :
    let local_dom := mkLocal n t s serial,
        locals := [local_dom],
        out := mkPi n t s body'
    in
    abstr body locals body'
    -> applyPi local_dom body out

-- identical to applyPi but for lambdas.
inductive applyLambda : ∀ (binder body out : Expr), Prop
| mk 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (body : Expr)
    (body' : Expr) :
    let local_dom := mkLocal n t s serial,
        locals := [local_dom],
        out := mkLambda n t s body'
    in
    abstr body locals body'
    -> applyLambda local_dom body out


inductive foldPis : ∀ (binders : list Expr) (e e' : Expr), Prop
| base (body : Expr) : 
    let binders : list Expr := [] 
    in foldPis binders body body

| step 
    (binders_hd : Expr)
    (binders_tl : list Expr)
    (body : Expr)
    (sink : Expr)
    (e' : Expr) :
    let binders := binders_hd :: binders_tl
    in
    foldPis binders_tl body sink
    -> applyPi binders_hd sink e'
    -> foldPis binders body e'

 inductive foldLambdas : ∀ (binders : list Expr) (e e' : Expr), Prop
| base (body : Expr) : 
    let binders : list Expr := [] 
    in foldLambdas binders body body

| step 
    (binders_hd : Expr)
    (binders_tl : list Expr)
    (body : Expr)
    (sink : Expr)
    (e' : Expr) :
    let binders := binders_hd :: binders_tl
    in
    foldLambdas binders_tl body sink
    -> applyLambda binders_hd sink e'
    -> foldLambdas binders body e'
         

inductive foldlApps : ∀ (f : Expr) (args : list Expr) (app : Expr), Prop
| base (base : Expr) : 
    let args : list Expr := []
    in
    foldlApps base args base
| step 
    (base : Expr)
    (hd : Expr)
    (tl : list Expr) 
    (folded : Expr) :
    let app := mkApp base hd,
        args := hd :: tl
    in
    foldlApps app tl folded
    -> foldlApps base args folded

inductive unfoldAppsAux : 
    ∀ (e : Expr)
      (args : list Expr)
      (result : (Expr × list Expr)),
      Prop
| base (f : Expr) (args : list Expr) : 
  let result := (f, args)
  in
  isApp f ff 
  -> unfoldAppsAux f args result

| step 
    (f : Expr)
    (a : Expr)
    (args : list Expr)
    (result : (Expr × list Expr)) :
    let args' := a :: args,
        e := mkApp f a
    in
    unfoldAppsAux f args' result
    -> unfoldAppsAux e args result

def unfoldApps (e : Expr) (result : Expr × list Expr) := 
  unfoldAppsAux e [] result


inductive telescopeSize : ∀ (e : Expr) (sz : nat), Prop
| base (e : Expr) : let sz := 0 in isPi e ff -> telescopeSize e sz
| step 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (sz : nat) :
    let e := mkPi n t s b
    in
    telescopeSize b (sz - 1)
    -> telescopeSize e sz


/-
Used to fold inferred lambdas into pi types.
`b_types` has the inferred binder types that actually end up being
the binder types for the pi/telescope, but we need `local_binders`
since that's what's holding the binder name and binder style
that we need to recover.
-/
inductive foldPisOnce : ∀ (b_types local_binders : list Expr) (abstrd out : Expr), Prop
| base (out : Expr) : 
    let b_types : list Expr := [],
        local_binders : list Expr := []
    in
    foldPisOnce b_types local_binders out out
| step 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (body : Expr)
    (serial : nat)
    (ts : list Expr)
    (unused_t : Expr)
    (local_binders : list Expr)
    (out : Expr) :
    let local_expr := mkLocal n unused_t s serial,
        local_binders' := local_expr :: local_binders,
        ts' := t :: ts,
        folded_pi := mkPi n t s body
    in
    foldPisOnce ts local_binders folded_pi out
    -> foldPisOnce ts' local_binders' body out


lemma tel0 : telescopeSize (mkSort Zero) 0 :=
begin
   apply telescopeSize.base (mkSort Zero),
   apply isPi.sort,
end

lemma tel1 : telescopeSize (mkPi (Anon) (mkSort (Succ Zero)) (Bstyle.Default) (mkSort Zero)) 1 :=
begin
  intros,
  apply telescopeSize.step Anon (mkSort (Succ Zero)) (Bstyle.Default) (mkSort Zero) 1 tel0,
end

def s0 := (mkSort Zero)
def s1 := mkSort (Succ Zero)
def s2 := mkSort (Succ (Succ Zero))
def f_small := (mkApp s0 s1)
def f_large := (mkApp f_small s2)

lemma unfold1 : unfoldAppsAux s0 [s1, s2] (s0, [s1, s2]) :=
begin
  apply unfoldAppsAux.base,
  apply isApp.sort,
end

lemma unfold2 : unfoldAppsAux (mkApp s0 s1) [s2] (s0, [s1, s2]) :=
begin
  intros,
  apply unfoldAppsAux.step s0 s1 [s2] (s0, [s1, s2]) unfold1,
end

lemma unfold3 : unfoldAppsAux (mkApp (mkApp s0 s1) s2) [] (s0, [s1, s2]) :=
begin
  intros,
  apply unfoldAppsAux.step (mkApp s0 s1) s2 [] (s0, [s1, s2]) unfold2,
end

lemma unfold4 : unfoldAppsAux (mkApp (mkApp s0 s1) s2) [] (s0, [s1, s2]) := unfold3


end Expr
