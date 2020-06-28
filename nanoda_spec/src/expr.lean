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

def mkPi 
    (n : Name) 
    (t : Expr) 
    (s : Bstyle)
    (b : Expr) 
    : Expr := 
    let bound := max (t.var_bound) (pred b.var_bound),
    locals := t.has_locals || b.has_locals
    in pi n t s b bound locals

def mkLambda 
    (n : Name) 
    (t : Expr) 
    (s : Bstyle)
    (b : Expr) 
    : Expr := 
    let bound := max (t.var_bound) (pred b.var_bound),
    locals := t.has_locals || b.has_locals
    in lambda n t s b bound locals

def mkLet 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (v : Expr)
    (b : Expr) 
    : Expr := 
    let bound := max (max (var_bound t) (var_bound v)) (pred b.var_bound),
    locals := has_locals t || has_locals v || has_locals b
    in letE n t s v b bound locals

def mkLocal 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    : Expr := 
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


inductive instAux : Expr -> list Expr -> nat -> Expr -> Prop
| noBound 
    (e : Expr)
    (subs : list Expr)
    (offset : nat)
    : var_bound e ≤ offset 
    -> instAux e subs offset e

| varHit 
    (dbj : nat)
    (subs : list Expr)
    (offset : nat)
    (e' : Expr)
    : listGet subs (dbj - offset) (some e')
    -> instAux (mkVar dbj) subs offset e'

| varMiss 
    (dbj : nat)
    (subs : list Expr)
    (offset : nat)
    : listGet subs (dbj - offset) none
    -> instAux (mkVar dbj) subs offset (mkVar dbj)

| app 
    (f a : Expr) 
    (subs : list Expr)
    (offset : nat) 
    (f' a' : Expr)
    : instAux f subs offset f'
    -> instAux a subs offset a'
    -> instAux (mkApp f a) subs offset (mkApp f' a')
                       
| pi 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' body' : Expr)
    : instAux t subs offset t'
    -> instAux body subs (1 + offset) body'
    -> instAux (mkPi n t s body) 
    subs
    offset 
    (mkPi n t' s body')

| lambda 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' body' : Expr)
    : instAux t subs offset t'
    -> instAux body subs (1 + offset) body'
    -> instAux (mkLambda n t s body) subs offset (mkLambda n t' s body')

| letE 
    (n : Name)
    (s : Bstyle)
    (t : Expr)
    (val : Expr)
    (body : Expr)
    (subs : list Expr)
    (offset : nat)
    (t' val' body' : Expr)
    : instAux t subs offset t'
      -> instAux val subs offset val'
      -> instAux body subs (1 + offset) body'
      -> instAux (mkLet n t s val body) subs offset (mkLet n t' s val' body')

inductive inst : Expr -> list Expr -> Expr -> Prop
| noBound (e : Expr) (subs : list Expr) (e' : Expr) : var_bound e = 0 -> inst e subs e
| byAux (e : Expr) (subs : list Expr) (e' : Expr) : instAux e subs 0 e' -> inst e subs e'

def inst1 (e sub e' : Expr) : Prop := inst e [sub] e'


inductive abstrAux : Expr -> list Expr -> nat -> Expr -> Prop
| noLocals 
    (e : Expr)
    (locals : list Expr)
    (offset : nat)
    : has_locals e = false
    -> abstrAux e locals offset e
           
| cacheHit 
    (e : Expr)
    (locals : list Expr)
    (offset : nat)
    (e' : Expr)
    : abstrAux e locals offset e' 
    -> abstrAux e locals offset e'

| localHit 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (locals : list Expr)
    (offset : nat)
    (pos : nat)
    : let ind_arg1 := mkLocal n t s serial
    in listPos ind_arg1 locals (some pos)
    -> abstrAux ind_arg1 locals offset (mkVar $ offset + pos)

| localMiss 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (locals : list Expr)
    (offset : nat)
    : let k := mkLocal n t s serial
    in listPos k locals none
    -> abstrAux k locals offset k

| app 
    (f a : Expr) 
    (locals : list Expr)
    (offset : nat) 
    (f' a' : Expr)
    : abstrAux f locals offset f'
    -> abstrAux a locals offset a'
    -> abstrAux (mkApp f a) locals offset (mkApp f' a')

| pi 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' body' : Expr)
    : abstrAux t locals offset t'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux (mkPi n t s body) locals offset (mkPi n t' s body')

| lambda 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' body' : Expr)
    : abstrAux t locals offset t'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux (mkLambda n t s body) locals offset (mkLambda n t' s body')

| letE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (val : Expr)
    (body : Expr)
    (locals : list Expr)
    (offset : nat) 
    (t' val' body' : Expr)
    : abstrAux t locals offset t'
    -> abstrAux val locals offset val'
    -> abstrAux body locals (1 + offset) body'
    -> abstrAux (mkLet n t s val body) locals offset (mkLet n t' s val' body')                  

  
  
  
inductive abstr : Expr -> list Expr -> Expr -> Prop
| noLocals (e : Expr) (subs : list Expr) : has_locals e = false -> abstr e subs e
| byAux 
    (e : Expr) 
    (subs : list Expr) 
    (e' : Expr) 
    : abstrAux e subs 0 e'
    -> abstr e subs e'


-- "beta" substitution for levels in an expression (Sort/Const exprs)
inductive subst : Expr -> list Level -> list Level -> Expr -> Prop
| var 
    (dbj : nat) 
    (ks vs : list Level) 
    : subst (mkVar dbj) ks vs (mkVar dbj)

| sort 
    (l : Level) 
    (ks vs : list Level) 
    (l' : Level)
    : l.subst ks vs l'
    -> subst (mkSort l) ks vs (mkSort l')

| const 
    (n : Name) 
    (levels ks vs levels' : list Level) 
    : Level.substMany ks vs levels levels'                                                 
    -> subst (mkConst n levels) ks vs (mkConst n levels')

| app 
    (f a : Expr) 
    (ks vs : list Level)
    (f' a' : Expr)
    : subst f ks vs f' 
    -> subst a ks vs a' 
    -> subst (mkApp f a) ks vs (mkApp f' a')

| pi 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (ks vs : list Level)
    (t' body' : Expr)
    : subst t ks vs t' 
    -> subst body ks vs body'
    -> subst (mkPi n t s body) ks vs (mkPi n t' s body')

| lambda 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (body : Expr)
    (ks vs : list Level)
    (t' body' : Expr)
    : subst t ks vs t' 
    -> subst body ks vs body'
    -> subst (mkLambda n t s body) ks vs (mkLambda n t' s body')

| letE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle) 
    (val : Expr)
    (body : Expr)
    (ks vs : list Level)
    (t' val' body' : Expr)
    : subst t ks vs t' 
    -> subst val ks vs val'
    -> subst body ks vs body'
    -> subst (mkLet n t s val body) ks vs (mkLet n t' s val' body')           

| localE 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat) 
    (ks vs : list Level)
    (t' : Expr)
    (serial' : nat)
    : subst t ks vs t' 
    -> subst (mkLocal n t s serial) ks vs (mkLocal n t' s serial')



inductive hasIndOcc : Expr -> list Name -> bool -> Prop
| var (dbj : nat) (ind_names : list Name) : hasIndOcc (var dbj) ind_names ff
    
| sort (l : Level) (ind_names : list Name) : hasIndOcc (sort l) ind_names ff

| const 
    (n : Name)
    (levels : list Level)
    (ind_names : list Name)
    (b : bool)
    : listMem n ind_names b
    -> hasIndOcc (mkConst n levels) ind_names b

| app 
    (f a : Expr)
    (ind_names : list Name)
    (b1 b2 : bool) 
    : hasIndOcc f ind_names b1
    -> hasIndOcc a ind_names b2
    -> hasIndOcc (mkApp f a) ind_names (b1 || b2)

| pi 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (body : Expr)
    (b1 b2 : bool) 
    (ind_names : list Name) 
    : hasIndOcc t ind_names b1
    -> hasIndOcc body ind_names b2
    -> hasIndOcc (mkPi n t s body) ind_names (b1 || b2)

| lambda 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (body : Expr)
    (b1 b2 : bool) 
    (ind_names : list Name) 
    : hasIndOcc t ind_names b1
    -> hasIndOcc body ind_names b2
    -> hasIndOcc (mkLambda n t s body) ind_names (b1 || b2)
                            
| letE   
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (val : Expr)
    (body : Expr)
    (b1 b2 b3 : bool) 
    (ind_names : list Name) 
    : hasIndOcc t ind_names b1
    -> hasIndOcc val ind_names b2
    -> hasIndOcc body ind_names b3
    -> hasIndOcc (mkLet n t s val body) ind_names (b1 || b2 || b3)
                            
| localE 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (b : bool) 
    (ind_names : list Name) 
    : hasIndOcc t ind_names b
    -> hasIndOcc (mkLocal n t s serial) ind_names b



inductive applyPi : Expr -> Expr -> Expr -> Prop
| mk 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (body : Expr)
    (body' : Expr)
    : let local_dom := mkLocal n t s serial
    in
    abstr body [local_dom] body'
    -> applyPi local_dom body (mkPi n t s body')

inductive applyLambda : Expr -> Expr -> Expr -> Prop
| mk 
    (n : Name) 
    (t : Expr)
    (s : Bstyle)
    (serial : nat)
    (body : Expr)
    (body' : Expr)
    : let local_dom := mkLocal n t s serial
    in
    abstr body [local_dom] body'
    -> applyLambda local_dom body (mkLambda n t s body')        


inductive foldPis : list Expr -> Expr -> Expr -> Prop
| base (body : Expr) : foldPis [] body body
| step 
    (doms_hd : Expr)
    (doms_tl : list Expr)
    (body : Expr)
    (sink : Expr)
    (out : Expr)
    : foldPis doms_tl body sink
    -> applyPi doms_hd sink out
    -> foldPis (doms_hd :: doms_tl) body out
      

inductive foldLambdas : list Expr -> Expr -> Expr -> Prop
| base (body : Expr) : foldLambdas [] body body
| step 
    (doms_hd : Expr)
    (doms_tl : list Expr)
    (body : Expr)
    (sink : Expr)
    (out : Expr)
    : foldLambdas doms_tl body sink
    -> applyLambda doms_hd sink out
    -> foldLambdas (doms_hd :: doms_tl) body out


inductive foldlApps : Expr -> list Expr -> Expr -> Prop
| base (base : Expr) : foldlApps base [] base
| step 
    (base : Expr)
    (hd : Expr)
    (tl : list Expr) 
    (folded : Expr)
    : foldlApps (mkApp base hd) tl folded
    -> foldlApps base (hd :: tl) folded



inductive unfoldAppsAux : Expr -> list Expr -> Expr -> list Expr -> Prop
| base (f : Expr) (args : list Expr) : isApp f ff -> unfoldAppsAux f args f args
| step 
    (f : Expr)
    (a : Expr)
    (sink : list Expr)
    (base_f : Expr)
    (all_args : list Expr)
    : unfoldAppsAux f (a :: sink) base_f all_args
    -> unfoldAppsAux (mkApp f a) (sink) base_f all_args

def unfoldApps (e base_f : Expr) (all_args : list Expr) := unfoldAppsAux e [] base_f all_args


inductive telescope_size : Expr -> nat -> Prop
| base (e : Expr) : isPi e ff -> telescope_size e 0
| step 
    (t e : Expr)
    (n : Name)
    (s : Bstyle)
    (sz : nat) 
    : telescope_size e sz
    -> telescope_size (mkPi n t s e) (1 + sz)


inductive foldPisOnce : list Expr -> list Expr -> Expr -> Expr -> Prop
| base (out : Expr) : foldPisOnce [] [] out out
| step 
    (t : Expr)
    (ts : list Expr)
    (n : Name)
    (unused_t : Expr)
    (s : Bstyle)
    (serial : nat)
    (local_binders : list Expr)
    (body : Expr)
    (folded : Expr)
    : foldPisOnce ts local_binders (mkPi n t s body) folded
    -> foldPisOnce (t :: ts) ((mkLocal n unused_t s serial) :: local_binders) body folded


lemma tel0 : telescope_size (mkSort z) 0 :=
begin
   apply telescope_size.base (mkSort z),
   apply isPi.sort,
end

lemma tel1 : telescope_size (mkPi (Anon) (mkSort (s z)) (Bstyle.Default) (mkSort z)) 1 :=
begin
  intros,
  apply telescope_size.step (mkSort (s z)) (mkSort z) (Anon) (Bstyle.Default) 0 tel0,
end




def s0 := (mkSort z)
def s1 := mkSort (s z)
def s2 := mkSort (s (s z))
def f_small := (mkApp s0 s1)
def f_large := (mkApp f_small s2)

lemma unfold1 : unfoldAppsAux s0 [s1, s2] s0 [s1, s2] :=
begin
  apply unfoldAppsAux.base,
  apply isApp.sort,
end

lemma unfold2 : unfoldAppsAux (mkApp s0 s1) [s2] s0 [s1, s2] :=
begin
  intros,
  apply unfoldAppsAux.step s0 s1 [s2] s0 [s1, s2] unfold1,
end

lemma unfold3 : unfoldAppsAux (mkApp (mkApp s0 s1) s2) [] s0 [s1, s2] :=
begin
  intros,
  apply unfoldAppsAux.step (mkApp s0 s1) s2 [] s0 [s1, s2] unfold2,
end

lemma unfold4 : unfoldApps (mkApp (mkApp s0 s1) s2) (s0) [s1, s2] := unfold3


end Expr

