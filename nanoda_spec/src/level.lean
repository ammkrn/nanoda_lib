import .name

inductive Level
| z : Level
| s  (pred : Level) : Level
| m  (l : Level) (r : Level) : Level
| im (l : Level) (r : Level) : Level
| p  (n : Name) : Level

instance : decidable_eq Level := by tactic.mk_dec_eq_instance

namespace Level


def mkSucc (l : Level) : Level := s l

def mkMax (a b : Level) : Level := m a b

def mkImax (a b : Level) : Level := im a b

def mkParam (n : Name) : Level := p n

inductive isZeroLit : Level -> bool -> Prop
| zero               : isZeroLit z tt
| succ (l : Level)   : isZeroLit (s l) ff
| max (l r : Level)  : isZeroLit (m l r) ff
| imax (l r : Level) : isZeroLit (im l r) ff
| param (n : Name)   : isZeroLit (p n) ff


inductive isSucc : Level -> bool -> Prop
| zero               : isSucc z ff
| succ (l : Level)   : isSucc (s l) tt
| max (l r : Level ) : isSucc (m l r) ff
| imax (l r : Level) : isSucc (im l r) ff
| param (n : Name)   : isSucc (p n) ff


inductive isAnyMax : Level -> bool -> Prop
| zero               : isAnyMax z ff
| succ (l : Level)   : isAnyMax (s l) ff
| max  (l r : Level) : isAnyMax (m l r) tt
| imax (l r : Level) : isAnyMax (im l r) tt
| param (n : Name)   : isAnyMax (p n) ff

-- lhs -> rhs -> result
inductive combining : Level -> Level -> Level -> Prop
| lzero (r : Level) : combining z r r
| rzero (l : Level) : combining l z l
| succ (l r x : Level) : combining l r x -> combining (s l) (s r) (s x)
| owise (l r : Level)
    : isZeroLit l ff
    → isZeroLit r ff
    -> isSucc l ff
    -> isSucc r ff
    -> combining l r (m l r)

inductive simplify : Level -> Level -> Prop
| zero : simplify z z
| param (n : Name) : simplify (p n) (p n)
| succ (l l' : Level) : simplify l l' -> simplify (s l) (s l')
| max (l r l' r' x : Level)
    : simplify l l'
    -> simplify r r'
    -> combining l' r' x
    -> simplify (m l r) x

| imaxzero (l r : Level) : simplify r z -> simplify (im l r) z

| imaxsucc (l r l' r' x : Level)
    : simplify r (s r')
    -> simplify l l'
    -> combining l' (s r') x
    -> simplify (im l r) x

| imaxowise (l r l' r' : Level)
    : simplify r r'
    -> isZeroLit r' ff
    -> isSucc r' ff
    -> simplify l l'
    -> simplify (im l r) (im l' r')


-- This doesn't have a false branch since it's used as an assertion
-- that all universe parameters in a given declaration are defined.
inductive paramsDefined : Level -> list Level -> Prop
| baseZero (ls : list Level) : paramsDefined z ls
| stepS (l : Level) (ls : list Level) : paramsDefined l ls -> paramsDefined (s l) ls

| stepM (l r : Level) (ls : list Level)
    : paramsDefined l ls                                          
    -> paramsDefined r ls
    -> paramsDefined (m l r) ls

| stepIm (l r : Level) (ls : list Level) 
    : paramsDefined l ls                                          
    -> paramsDefined r ls
    -> paramsDefined (im l r) ls
| baseParam (n : Name) (hd : Level) (tl : list Level) : paramsDefined (p n) (p n :: tl)

| stepParam 
    (n : Name)
    (hd : Level)
    (tl : list Level) 
    : paramsDefined (p n) tl
    -> paramsDefined (p n) (hd :: tl)

inductive paramsDefinedMany : list Level -> list Level -> Prop 
| base (dec_ups : list Level) : paramsDefinedMany [] dec_ups
| step (hd : Level) (tl dec_ups : list Level) 
    : paramsDefinedMany tl dec_ups
    -> paramsDefined hd dec_ups
    -> paramsDefinedMany (hd :: tl) dec_ups


                          

inductive subst : Level -> list Level -> list Level -> Level -> Prop
| mkZero (ks vs : list Level) : subst z ks vs z

| mkSucc (pred pred' : Level) (ks vs : list Level) 
    : subst pred ks vs pred'
    -> subst (s pred) ks vs (s pred')

| mkMax (l r l' r' : Level) (ks vs : list Level) 
    : subst l ks vs l'
    -> subst r ks vs r'
    -> subst (m l r) ks vs (m l' r')

| mkImax (l r l' r' : Level) (ks vs : list Level) 
    : subst l ks vs l'
    -> subst r ks vs r'
    -> subst (im l r) ks vs (im l' r')

| mkParamNil (n : Name) : subst (p n) [] [] (p n)
| mkParamEq 
    (n : Name) 
    (v : Level) 
    (ks_tl vs_tl : list Level) 
    : subst (p n) (p n :: ks_tl) (v :: vs_tl) v

| mkParamNe 
    (n : Name) 
    (k v l' : Level)
    (ks vs : list Level) 
    : p n ≠ k
    -> subst (p n) ks vs (l')
    -> subst (p n) (k :: ks) (v :: vs) (l')


inductive substMany : list Level -> list Level -> list Level -> list Level -> Prop 
| base (ks vs : list Level) : substMany [] ks vs []
| step (hd hd' : Level) 
       (ks vs ls ls' : list Level) 
       : substMany ls ks vs ls' 
       -> subst hd ks vs hd' 
       -> substMany (hd :: ls) ks vs (hd' :: ls')




-- Some cases look weird since `false : bool` is used to 
-- indicate that in some cases, we don't know whether L ≤ R.
-- A good example is the (p_z) constructor. In the case that
-- l_h and r_h were the same, then a substitution of zero for
-- the parameter in L would mean they're equal, but without knowing
-- what the substitution is/will be, we cannot say that L ≤ R,
-- so we return false.
inductive leqCore : Level -> Level -> nat -> nat -> bool -> Prop
| z_any (r : Level) (l_h r_h : nat) : l_h ≤ r_h -> leqCore z r l_h r_h tt
| any_z (l : Level) (l_h r_h : nat) : r_h < l_h -> leqCore l z l_h r_h ff
--| p_p (n : Name) (l_h r_h : nat) : l_h ≤ r_h -> leqCore (p n) (p n) l_h r_h tt
| p_p (n1 n2 : Name) (l_h r_h : nat) : leqCore (p n1) (p n2) l_h r_h ((n1 = n2) && (l_h ≤ r_h))
| p_z (n : Name) (l_h r_h : nat) : leqCore (p n) z l_h r_h ff
| z_p (n : Name) (l_h r_h : nat) : leqCore z (p n) l_h r_h (l_h ≤ r_h)
| s_any (l r : Level) (l_h r_h : nat) (b : bool) 
    : leqCore l r (nat.succ l_h) (r_h) b
    -> leqCore (s l) r l_h r_h b
| any_s (l r : Level) (l_h r_h : nat) (b : bool) 
    : leqCore l r l_h (nat.succ r_h) b
    -> leqCore l (s r) l_h r_h b

| max_any (a b r : Level) 
          (l_h r_h : nat) 
          (b1 b2 : bool)
          : leqCore a r l_h r_h b1
          -> leqCore b r l_h r_h b2
          -> leqCore (m a b) r l_h r_h (b1 && b2)
            
| p_max (n : Name)
       (x y : Level)
       (b1 b2 : bool)
       (l_h r_h : nat)
       : leqCore (p n) x l_h r_h b1
       -> leqCore (p n) y l_h r_h b2
       -> leqCore (p n) (m x y) l_h r_h (b1 || b2)

| z_max (x y : Level)
        (b1 b2 : bool)
        (l_h r_h : nat)
        : leqCore z x l_h r_h b1
        -> leqCore z y l_h r_h b2
        -> leqCore z (m x y) l_h r_h (b1 || b2)

| imim_congr (l r : Level) (l_h r_h : nat) : leqCore (im l r) (im l r) l_h r_h tt
-- im_p_any and any_imp_p inline `ensure_imax_leq` to avoid the need for mutuals.
| im_p_any (n : Name) 
           (a r l_z r_z l_s r_s l_z' r_z' l_s' r_s' : Level) 
           (l_h r_h : nat)
           (b1 b2 : bool) 
           : subst (im a (p n)) [p n] [z] l_z
           -> subst r [p n] [z] r_z
           -> simplify l_z l_z'
           -> simplify r_z r_z'
           -> subst (im a (p n)) [p n] [s $ p n] l_s
           -> subst r [p n] [s $ p n] r_s
           -> simplify l_s l_s'
           -> simplify r_s r_s'
           -> leqCore l_z' r_z' l_h r_h b1
           -> leqCore l_s' r_s' l_h r_h b2
           -> leqCore (im a (p n)) r l_h r_h (b1 && b2)

| any_im_p (n : Name)
           (x l l_z r_z l_s r_s l_z' r_z' l_s' r_s' : Level) 
           (l_h r_h : nat)
           (b1 b2 : bool) 
           : subst l [p n] [z] l_z
           -> subst (im x (p n)) [p n] [z] r_z
           -> simplify l_z l_z'
           -> simplify r_z r_z'
           -> subst l [p n] [s $ p n] l_s
           -> subst (im x (p n)) [p n] [s $ p n] r_s
           -> simplify l_s l_s'
           -> simplify r_s r_s'
           -> leqCore l_z' r_z' l_h r_h b1
           -> leqCore l_s' r_s' l_h r_h b2
           -> leqCore l (im x (p n)) l_h r_h (b1 && b2)

| imim_any (a c d r : Level)
           (l_h r_h : nat)
           (b : bool)
           : leqCore (m (im a d) (im c d)) r l_h r_h b
           -> leqCore (im a (im c d)) r l_h r_h b

| imm_any (a c d r new_max' : Level)
          (l_h r_h : nat)
          (b : bool)
          : simplify (m (im a c) (im a d)) new_max'
          -> leqCore new_max' r l_h r_h b
          -> leqCore (im a (m c d)) r l_h r_h b

| any_imim (l x j k : Level)
           (l_h r_h : nat)
           (b : bool)
           : leqCore l (m (im x k) (im j k)) l_h r_h b
           -> leqCore l (im x (im j k)) l_h r_h b

| any_imm (l x j k new_max' : Level)
          (l_h r_h : nat)
          (b : bool)
          : simplify (m (im x j) (im x k)) new_max'
          -> leqCore l new_max' l_h r_h b
          -> leqCore l (im x (m j k)) l_h r_h b

inductive leq : Level -> Level -> bool -> Prop
| mk (l r l' r' : Level) (b : bool) 
    : simplify l l' 
    -> simplify r r'
    -> leqCore l' r' 0 0 b
    -> leq l r b


inductive eqAntisymm : Level -> Level -> bool -> Prop
| mk (l r : Level) (b1 b2 : bool) 
    : leq l r b1 
    -> leq r l b2 
    -> eqAntisymm l r (b1 && b2)


inductive geq : Level -> Level -> bool -> Prop
| mk (l r : Level) (b1 b2 : bool) 
    : eqAntisymm l r b1
    -> leq r l b2 
    -> geq l r (b1 || b2)

inductive is_zero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : leq l z b -> is_zero l b

inductive is_nonzero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : leq (s z) l b -> is_nonzero l b

inductive maybe_zero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : is_nonzero l b -> maybe_zero l (¬b)

inductive maybe_nonzero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : is_zero l b -> maybe_nonzero l (¬b)

inductive eqAntisymmMany : list Level -> list Level -> bool -> Prop
| baseT : eqAntisymmMany [] [] tt
| baseFL (l : Level) (ls : list Level) : eqAntisymmMany (l :: ls) [] ff
| baseFR (r : Level) (rs : list Level) : eqAntisymmMany [] (r :: rs) ff
| step 
    (l r : Level) 
    (ls rs : list Level)
    (b1 b2 : bool)
    : eqAntisymm l r b1
    -> eqAntisymmMany ls rs b2
    -> eqAntisymmMany (l :: ls) (r :: rs) (b1 && b2)

/-
Used for inference of Pis. From ([C, B, A], L)
create
        Im
      /    \
     A      Im
           /  \
          B    Im
              /  \
             C    L
-/
inductive foldImaxs : list Level -> Level -> Level -> Prop
| base (out : Level) : foldImaxs [] out out
| step (hd : Level)
       (tl : list Level)
       (r : Level)
       (out : Level)
       : foldImaxs tl (im hd r) out
       -> foldImaxs (hd :: tl) r out

end Level
