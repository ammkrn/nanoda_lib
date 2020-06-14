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

| app (f : Expr) 
      (a : Expr)
      (var_bound : nat)
      (has_locals : bool) 
      : Expr

| pi  (b_n : Name) 
      (b_t : Expr) 
      (b_s : Bstyle) 
      (body : Expr)
      (var_bound : nat)
      (has_locals : bool) 
      : Expr
      
| lambda (b_n : Name) 
         (b_t : Expr) 
         (b_s : Bstyle) 
         (body : Expr)
         (var_bound : nat)
         (has_locals : bool) 
         : Expr

| letE (b_n : Name) 
       (b_t : Expr) 
       (b_s : Bstyle) 
       (val : Expr)
       (body : Expr)
       (var_bound : nat)
       (has_locals : bool) 
       : Expr

| localE (b_n : Name) 
         (b_t : Expr) 
         (b_s : Bstyle) 
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

def mkPi (b_n : Name) 
         (b_t : Expr) 
         (b_s : Bstyle)
         (body : Expr) 
         : Expr := 
   let bound := max (b_t.var_bound) (pred body.var_bound),
       locals := b_t.has_locals || body.has_locals
   in pi b_n b_t b_s body bound locals

def mkLambda (b_n : Name) 
             (b_t : Expr) 
             (b_s : Bstyle)
             (body : Expr) 
             : Expr := 
   let bound := max (b_t.var_bound) (pred $ body.var_bound),
       locals := b_t.has_locals || body.has_locals
   in lambda b_n b_t b_s body bound locals

def mkLet (b_n : Name)
          (b_t : Expr)
          (b_s : Bstyle)
          (val : Expr)
          (body : Expr) 
          : Expr := 
   let bound := max (max (var_bound b_t) (var_bound val)) (pred $ var_bound body),
       locals := has_locals b_t || has_locals val || has_locals body
   in letE b_n b_t b_s val body bound locals

def mkLocal (b_n : Name)
            (b_t : Expr)
            (b_s : Bstyle)
            (serial : nat)
            : Expr := localE b_n b_t b_s serial

-- Tracking/managing this is up to the implementation.
inductive nextSerial : nat -> Prop
            
inductive isApp : Expr -> bool -> Prop
| var (dbj : nat) : isApp (mkVar dbj) ff
| sort (l : Level) : isApp (mkSort l) ff
| const (n : Name) (ls : list Level) : isApp (mkConst n ls) ff
| app (f a : Expr) : isApp (mkApp f a) tt
| pi (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isApp (mkPi b_n b_t b_s body) ff
| lambda (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isApp (mkLambda b_n b_t b_s body) ff
| letE (b_n : Name) (b_t val body : Expr) (b_s : Bstyle) : isApp (mkLet b_n b_t b_s val body) ff
| localE (b_n : Name) (b_t : Expr) (b_s : Bstyle) (serial : nat) : isApp (mkLocal b_n b_t b_s serial) ff


inductive isPi : Expr -> bool -> Prop
| var (dbj : nat) : isPi (mkVar dbj) ff
| sort (l : Level) : isPi (mkSort l) ff
| const (n : Name) (ls : list Level) : isPi (mkConst n ls) ff
| app (f a : Expr) : isPi (mkApp f a) ff
| pi (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isPi (mkPi b_n b_t b_s body) tt
| lambda (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isPi (mkLambda b_n b_t b_s body) ff
| letE (b_n : Name) (b_t val body : Expr) (b_s : Bstyle) : isPi (mkLet b_n b_t b_s val body) ff
| localE (b_n : Name) (b_t : Expr) (b_s : Bstyle) (serial : nat) : isPi (mkLocal b_n b_t b_s serial) ff


inductive isLambda : Expr -> bool -> Prop
| var (dbj : nat) : isLambda (mkVar dbj) ff
| sort (l : Level) : isLambda (mkSort l) ff
| const (n : Name) (ls : list Level) : isLambda (mkConst n ls) ff
| app (f a : Expr) : isLambda (mkApp f a) ff
| pi (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isLambda (mkPi b_n b_t b_s body) ff
| lambda (b_n : Name) (b_t body : Expr) (b_s : Bstyle) : isLambda (mkLambda b_n b_t b_s body) tt
| letE (b_n : Name) (b_t val body : Expr) (b_s : Bstyle) : isLambda (mkLet b_n b_t b_s val body) ff
| localE (b_n : Name) (b_t : Expr) (b_s : Bstyle) (serial : nat) : isLambda (mkLocal b_n b_t b_s serial) ff


inductive instAux : Expr -> list Expr -> nat -> Expr -> Prop
| noBound (e : Expr)
          (subs : list Expr)
          (offset : nat)
          : var_bound e ≤ offset 
            -> instAux e subs offset e

| cacheHit (e : Expr) 
           (subs : list Expr) 
           (offset : nat) 
           (e' : Expr)
           : instAux e subs offset e'
             -> instAux e subs offset e'

| varHit (dbj : nat)
         (subs : list Expr)
         (offset : nat)
         (e' : Expr)
         : listGet subs (dbj - offset) (some e')
           -> instAux (mkVar dbj) subs offset e'

| varMiss (dbj : nat)
          (subs : list Expr)
          (offset : nat)
          : listGet subs (dbj - offset) none
            -> instAux (mkVar dbj) subs offset (mkVar dbj)

| app (f a : Expr) 
      (subs : list Expr)
      (offset : nat) 
      (f' a' : Expr)
      : instAux f subs offset f'
        -> instAux a subs offset a'
        -> instAux (mkApp f a) subs offset (mkApp f' a')
                       
| pi (b_n : Name)
     (b_s : Bstyle)
     (b_t : Expr)
     (body : Expr)
     (subs : list Expr)
     (offset : nat)
     (b_t' body' : Expr)
     : instAux b_t subs offset b_t'
       -> instAux body subs (1 + offset) body'
       -> instAux (mkPi b_n b_t b_s body) 
                  subs
                  offset 
                  (mkPi b_n b_t' b_s body')

| lambda (b_n : Name)
         (b_s : Bstyle)
         (b_t : Expr)
         (body : Expr)
         (subs : list Expr)
         (offset : nat)
         (b_t' body' : Expr)
         : instAux b_t subs offset b_t'
           -> instAux body subs (1 + offset) body'
           -> instAux (mkLambda b_n b_t b_s body) 
                      subs
                      offset 
                      (mkLambda b_n b_t' b_s body')

| letE (b_n : Name)
       (b_s : Bstyle)
       (b_t : Expr)
       (val : Expr)
       (body : Expr)
       (subs : list Expr)
       (offset : nat)
       (b_t' val' body' : Expr)
       : instAux b_t subs offset b_t'
         -> instAux val subs offset val'
         -> instAux body subs (1 + offset) body'
         -> instAux (mkLet b_n b_t b_s val body) 
                    subs
                    offset 
                    (mkLet b_n b_t' b_s val' body')

inductive inst : Expr -> list Expr -> Expr -> Prop
| noBound (e : Expr) (subs : list Expr) (e' : Expr) : var_bound e = 0 -> inst e subs e
| byAux (e : Expr) (subs : list Expr) (e' : Expr) : instAux e subs 0 e' -> inst e subs e'



inductive abstrAux : Expr -> list Expr -> nat -> Expr -> Prop
| noLocals (e : Expr)
           (locals : list Expr)
           (offset : nat)
           : has_locals e = false
             -> abstrAux e locals offset e
           
| cacheHit (e : Expr)
           (locals : list Expr)
           (offset : nat)
           (e' : Expr)
           : abstrAux e locals offset e' -> abstrAux e locals offset e'

| localHit (b_n : Name)
           (b_t : Expr)
           (b_s : Bstyle)
           (serial : nat)
           (locals : list Expr)
           (offset : nat)
           (pos : nat)
           : let ind_arg1 := mkLocal b_n b_t b_s serial
             in listPos ind_arg1 locals (some pos)
                 -> abstrAux ind_arg1 locals offset (mkVar $ offset + pos)

| localMiss (b_n : Name)
            (b_t : Expr)
            (b_s : Bstyle)
            (serial : nat)
            (locals : list Expr)
            (offset : nat)
            : let k := mkLocal b_n b_t b_s serial
              in listPos k locals none
                  -> abstrAux k locals offset k

| app (f a : Expr) 
      (locals : list Expr)
      (offset : nat) 
      (f' a' : Expr)
      : abstrAux f locals offset f'
        -> abstrAux a locals offset a'
        -> abstrAux (mkApp f a) locals offset (mkApp f' a')

| pi (b_n : Name) 
     (b_t : Expr)
     (b_s : Bstyle) 
     (body : Expr)
     (locals : list Expr)
     (offset : nat) 
     (b_t' body' : Expr)
     : abstrAux b_t locals offset b_t'
       -> abstrAux body locals (1 + offset) body'
       -> abstrAux (mkPi b_n b_t b_s body) locals offset (mkPi b_n b_t' b_s body')

| lambda (b_n : Name) 
         (b_t : Expr)
         (b_s : Bstyle) 
         (body : Expr)
         (locals : list Expr)
         (offset : nat) 
         (b_t' body' : Expr)
         : abstrAux b_t locals offset b_t'
           -> abstrAux body locals (1 + offset) body'
           -> abstrAux (mkLambda b_n b_t b_s body) locals offset (mkLambda b_n b_t' b_s body')

| letE (b_n : Name) 
       (b_t : Expr)
       (b_s : Bstyle) 
       (val : Expr)
       (body : Expr)
       (locals : list Expr)
       (offset : nat) 
       (b_t' val' body' : Expr)
       : abstrAux b_t locals offset b_t'
        -> abstrAux val locals offset val'
        -> abstrAux body locals (1 + offset) body'
        -> abstrAux (mkLet b_n b_t b_s val body) locals offset (mkLet b_n b_t' b_s val' body')                  

  
  
  
inductive abstr : Expr -> list Expr -> Expr -> Prop
| noLocals (e : Expr) (subs : list Expr) : has_locals e = false -> abstr e subs e
| byAux (e : Expr) 
        (subs : list Expr) 
        (e' : Expr) 
        : abstrAux e subs 0 e'
          -> abstr e subs e'


-- "beta" substitution for levels in an expression (Sort/Const exprs)
inductive subst : Expr -> list Level -> list Level -> Expr -> Prop
| cacheHit (e : Expr) 
           (ks vs : list Level)
           (e' : Expr)
           : subst e ks vs e' -> subst e ks vs e'
             
| var (dbj : nat) 
          (ks vs : list Level) 
          : subst (mkVar dbj) ks vs (mkVar dbj)

| sort (l : Level) 
         (ks vs : list Level) 
         (l' : Level)
         : l.subst ks vs l'
           -> subst (mkSort l) ks vs (mkSort l')

| const (n : Name) 
          (levels ks vs levels' : list Level) 
          : Level.substMany ks vs levels levels'                                                 
            -> subst (mkConst n levels) ks vs (mkConst n levels')

| app (f a : Expr) 
          (ks vs : list Level)
          (f' a' : Expr)
          : subst f ks vs f' 
            -> subst a ks vs a' 
            -> subst (mkApp f a) ks vs (mkApp f' a')

| pi (b_n : Name) 
         (b_t : Expr)
         (b_s : Bstyle) 
         (body : Expr)
         (ks vs : list Level)
         (b_t' body' : Expr)
         : subst b_t ks vs b_t' 
           -> subst body ks vs body'
           -> subst (mkPi b_n b_t b_s body) ks vs (mkPi b_n b_t' b_s body')

| lambda (b_n : Name) 
         (b_t : Expr)
         (b_s : Bstyle) 
         (body : Expr)
         (ks vs : list Level)
         (b_t' body' : Expr)
         : subst b_t ks vs b_t' 
           -> subst body ks vs body'
           -> subst (mkLambda b_n b_t b_s body) ks vs (mkLambda b_n b_t' b_s body')

| letE (b_n : Name) 
       (b_t : Expr)
       (b_s : Bstyle) 
       (val : Expr)
       (body : Expr)
       (ks vs : list Level)
       (b_t' val' body' : Expr)
       : subst b_t ks vs b_t' 
         -> subst val ks vs val'
         -> subst body ks vs body'
         -> subst (mkLet b_n b_t b_s val body) ks vs (mkLet b_n b_t' b_s val' body')           

| localE (b_n : Name) 
         (b_t : Expr)
         (b_s : Bstyle)
         (serial : nat) 
         (ks vs : list Level)
         (b_t' : Expr)
         (serial' : nat)
         : subst b_t ks vs b_t' 
           -> subst (mkLocal b_n b_t b_s serial) ks vs (mkLocal b_n b_t' b_s serial')



inductive hasIndOcc : Expr -> list Name -> bool -> Prop
| cacheHit (e : Expr) 
           (ind_names : list Name)
           (b : bool) 
           : hasIndOcc e ind_names b -> hasIndOcc e ind_names b

| var (dbj : nat)
      (ind_names : list Name) : hasIndOcc (var dbj) ind_names ff
    
| sort (l : Level)
       (ind_names : list Name) : hasIndOcc (sort l) ind_names ff

| const (n : Name)
        (levels : list Level)
        (ind_names : list Name)
        (b : bool)
        : listMem n ind_names b
          -> hasIndOcc (mkConst n levels) ind_names b

| app (f a : Expr)
      (ind_names : list Name)
      (b1 b2 : bool) 
      : hasIndOcc f ind_names b1
        -> hasIndOcc a ind_names b2
        -> hasIndOcc (mkApp f a) ind_names (b1 || b2)

| pi (b_n : Name)
     (b_t : Expr)
     (b_s : Bstyle)
     (body : Expr)
     (b1 b2 : bool) 
     (ind_names : list Name) 
     : hasIndOcc b_t ind_names b1
       -> hasIndOcc body ind_names b2
       -> hasIndOcc (mkPi b_n b_t b_s body) ind_names (b1 || b2)

| lambda (b_n : Name)
         (b_t : Expr)
         (b_s : Bstyle)
         (body : Expr)
         (b1 b2 : bool) 
         (ind_names : list Name) 
         : hasIndOcc b_t ind_names b1
           -> hasIndOcc body ind_names b2
           -> hasIndOcc (mkLambda b_n b_t b_s body) ind_names (b1 || b2)
                            
| letE   (b_n : Name)
         (b_t : Expr)
         (b_s : Bstyle)
         (val : Expr)
         (body : Expr)
         (b1 b2 b3 : bool) 
         (ind_names : list Name) 
         : hasIndOcc b_t ind_names b1
           -> hasIndOcc val ind_names b2
           -> hasIndOcc body ind_names b3
           -> hasIndOcc (mkLet b_n b_t b_s val body) ind_names (b1 || b2 || b3)
                            
| localE (b_n : Name)
         (b_t : Expr)
         (b_s : Bstyle)
         (serial : nat)
         (b : bool) 
         (ind_names : list Name) 
         : hasIndOcc b_t ind_names b
           -> hasIndOcc (mkLocal b_n b_t b_s serial) ind_names b



inductive applyPi : Expr -> Expr -> Expr -> Prop
| mk (b_n : Name) 
     (b_t : Expr)
     (b_s : Bstyle)
     (serial : nat)
     (body : Expr)
     (body' : Expr)
     :  let local_dom := mkLocal b_n b_t b_s serial
        in
        abstr body [local_dom] body'
        -> applyPi local_dom body (mkPi b_n b_t b_s body')

inductive applyLambda : Expr -> Expr -> Expr -> Prop
| mk (b_n : Name) 
     (b_t : Expr)
     (b_s : Bstyle)
     (serial : nat)
     (body : Expr)
     (body' : Expr)
     :  let local_dom := mkLocal b_n b_t b_s serial
        in
        abstr body [local_dom] body'
        -> applyLambda local_dom body (mkLambda b_n b_t b_s body')        


inductive foldPis : list Expr -> Expr -> Expr -> Prop
| base (body : Expr) : foldPis [] body body
| step (doms_hd : Expr)
       (doms_tl : list Expr)
       (body : Expr)
       (sink : Expr)
       (out : Expr)
       : foldPis doms_tl body sink
         -> applyPi doms_hd sink out
         -> foldPis (doms_hd :: doms_tl) body out
      

inductive foldLambdas : list Expr -> Expr -> Expr -> Prop
| base (body : Expr) : foldLambdas [] body body
| step (doms_hd : Expr)
       (doms_tl : list Expr)
       (body : Expr)
       (sink : Expr)
       (out : Expr)
       : foldLambdas doms_tl body sink
         -> applyLambda doms_hd sink out
         -> foldLambdas (doms_hd :: doms_tl) body out


inductive foldlApps : Expr -> list Expr -> Expr -> Prop
| base (base : Expr) : foldlApps base [] base
| step (base : Expr)
       (hd : Expr)
       (tl : list Expr) 
       (folded : Expr)
       : foldlApps (mkApp base hd) tl folded
         -> foldlApps base (hd :: tl) folded



inductive unfoldAppsAux : Expr -> list Expr -> Expr -> list Expr -> Prop
| base (f : Expr) (args : list Expr) : isApp f ff -> unfoldAppsAux f args f args
| step (f : Expr)
       (a : Expr)
       (sink : list Expr)
       (base_f : Expr)
       (all_args : list Expr)
       : unfoldAppsAux f (a :: sink) base_f all_args
         -> unfoldAppsAux (mkApp f a) (sink) base_f all_args

def unfoldApps (e base_f : Expr) (all_args : list Expr) := unfoldAppsAux e [] base_f all_args


inductive telescope_size : Expr -> nat -> Prop
| base (e : Expr) : isPi e ff -> telescope_size e 0
| step (b_t e : Expr)
       (b_n : Name)
       (b_s : Bstyle)
       (n : nat) 
       : telescope_size e n 
         -> telescope_size (mkPi b_n b_t b_s e) (1 + n)



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

