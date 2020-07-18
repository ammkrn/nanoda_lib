import .name

inductive Level
| Zero : Level
| Succ  (pred : Level) : Level
| Max  (l : Level) (r : Level) : Level
| Imax (l : Level) (r : Level) : Level
| Param  (n : Name) : Level

instance : decidable_eq Level := by tactic.mk_dec_eq_instance

namespace Level

def mkSucc (l : Level) : Level := Succ l

def mkMax (a b : Level) : Level := Max a b

def mkImax (a b : Level) : Level := Imax a b

def mkParam (n : Name) : Level := Param n

inductive isZeroLit : ∀ (l : Level) (result : bool), Prop
| ofZero : 
    let l := Zero,
        result := tt
    in isZeroLit l result
| ofSucc (pred : Level) :
    let l := Succ pred,
        result := ff
    in isZeroLit l result
| ofMax (fst snd : Level) : 
    let l := Max fst snd,
        result := ff
    in isZeroLit l result
| ofImax (fst snd : Level) : 
    let l := Imax fst snd,
        result := ff
    in isZeroLit l result
| ofParam (n : Name) : 
    let l := Param n,
        result := ff
    in isZeroLit l result

inductive isSucc : ∀ (l : Level) (result : bool), Prop
| ofZero : 
    let l := Zero,
        result := ff 
    in 
    isSucc l result

| ofSucc (pred : Level) : 
    let l := Succ pred,
        result := tt
    in isSucc l result

| ofMax (fst snd : Level ) : 
    let l := Max fst snd,
        result := ff
    in isSucc l result

| ofImax (fst snd : Level) : 
    let l := Imax fst snd,
        result := ff
    in isSucc l result

| ofParam (n : Name) : 
    let l := Param n,
        result := ff
    in isSucc l result


inductive isAnyMax : ∀ (l : Level) (result : bool), Prop
| ofZero : 
    let l := Zero,
        result := ff
    in isAnyMax l result
| ofSucc (pred : Level) : 
    let l := Succ pred,
        result := ff
    in isAnyMax l result
| ofMax  (fst snd : Level) : 
    let l := Max fst snd,
        result := tt
    in isAnyMax l result
| ofImax (fst snd : Level) : 
    let l := Imax fst snd,
        result := tt
    in isAnyMax l result
| ofParam (n : Name) : 
    let l := Param n,
        result := ff
    in isAnyMax l result

inductive combining : ∀ (l : Level) (r : Level) (result : Level), Prop
| lzero (r : Level) : 
    let l := Zero,
        result := r
    in combining l r result
| rzero (l : Level) : 
    let r := Zero,
        result := l
    in combining l r result
| succ 
    (l_pred : Level)
    (r_pred : Level)
    (result' : Level) : 
    let l := Succ l_pred,
        r := Succ r_pred,
        result := Succ result'
    in
    combining l_pred r_pred result' 
    -> combining l r result

| owise (l r : Level) : 
    let result := Max l r
    in
    isZeroLit l ff
    -> isZeroLit r ff
    -> isSucc l ff
    -> isSucc r ff
    -> combining l r result

inductive simplify : ∀ (l : Level) (result : Level), Prop
| zero : 
    let l := Zero,
        result := Zero
    in simplify l result

| param (n : Name) : 
    let l := Param n,
        result := Param n
    in simplify l result

| succ (pred : Level) (pred' : Level) : 
    let l := Succ pred,
        result := Succ pred'
    in
    simplify pred pred'
    -> simplify l result

| max 
    (fst : Level)
    (snd : Level)
    (fst' : Level)
    (snd' : Level)
    (result : Level) : 
    let l := Max fst snd
    in
    simplify fst fst'
    -> simplify snd snd'
    -> combining fst' snd' result
    -> simplify (Max fst snd) result

| imaxzero (fst : Level) (snd : Level) : 
    let l := Imax fst snd,
        snd' := Zero,
        result := Zero
    in
    simplify snd snd'
    -> simplify l result

| imaxsucc 
    (fst : Level)
    (snd : Level)
    (fst' : Level)
    (snd' : Level)
    (result : Level) :
    let l := Imax fst snd,
        succ_snd' := Succ snd'
    in
    simplify snd succ_snd'
    -> simplify fst fst'
    -> combining fst' succ_snd' result
    -> simplify l result

| imaxowise 
    (fst : Level)
    (snd : Level)
    (fst' : Level)
    (snd' : Level) :
    let l := Imax fst snd,
        result := Imax fst' snd'
    in
    simplify snd snd'
    -> isZeroLit snd' ff
    -> isSucc snd' ff
    -> simplify fst fst'
    -> simplify l result



-- The implementation/output also outputs a bool, but it should always
-- be true.
-- that all universe parameters in a given declaration are defined.
inductive paramsDefined : ∀ (l : Level) (params : list Level), Prop
| zero (params : list Level) : 
    let l := Zero in paramsDefined l params

| succ (pred : Level) (params : list Level) : 
    let l := Succ pred
    in 
    paramsDefined pred params -> paramsDefined l params

| max (fst snd : Level) (params : list Level) :
    let l := Max fst snd
    in
    paramsDefined fst params
    -> paramsDefined snd params
    -> paramsDefined l params

| imax (fst : Level) (snd : Level) (params : list Level) :
    let l := Imax fst snd
    in
    paramsDefined fst params
    -> paramsDefined snd params
    -> paramsDefined l params

| baseParam (n : Name) (tl : list Level) : 
    let l := Param n,
        params := l :: tl
    in
    paramsDefined l params

| stepParam (n : Name) (hd : Level) (tl : list Level) :
    let l := Param n,
        params := hd :: tl
    in
    paramsDefined l tl
    -> paramsDefined l params

inductive paramsDefinedMany : ∀ (ls : list Level) (params : list Level), Prop 
| base (params : list Level) : 
    let ls : list Level := []
    in
    paramsDefinedMany ls params

| step (hd : Level) (tl : list Level) (params : list Level) :
    let ls := hd :: tl
    in
    paramsDefinedMany tl params
    -> paramsDefined hd params
    -> paramsDefinedMany ls params


                          

inductive subst : ∀ (l : Level) (ks : list Level) (vs : list Level) (l' : Level), Prop
| zero (ks : list Level) (vs : list Level) : 
    let l := Zero,
        l' := Zero
    in
    subst l ks vs l'

| succ 
    (pred : Level)
    (pred' : Level)
    (ks : list Level)
    (vs : list Level) : 
    let l := Succ pred,
        l' := Succ pred'
    in
    subst pred ks vs pred'
    -> subst l ks vs l'

| max
    (fst : Level)
    (snd : Level)
    (fst' : Level)
    (snd' : Level)
    (ks : list Level)
    (vs : list Level) :
    let l := Max fst snd,
        l' := Max fst' snd'
    in
    subst fst ks vs fst'
    -> subst snd ks vs snd'
    -> subst l ks vs l'

| imax
    (fst : Level)
    (snd : Level)
    (fst' : Level)
    (snd' : Level)
    (ks : list Level)
    (vs : list Level) :
    let l := Imax fst snd,
        l' := Imax fst' snd'
    in
    subst fst ks vs snd'
    -> subst snd ks vs snd'
    -> subst l ks vs l'

| paramNil (n : Name) : 
    let l := Param n,
        ks : list Level := [],
        vs : list Level := []
    in
    subst l ks vs l

| paramEq 
    (n : Name) 
    (v : Level) 
    (ks_tl : list Level)
    (vs_tl : list Level) :
    let l := Param n,
        ks := l :: ks_tl,
        vs := v :: vs_tl
    in
    subst l ks vs v

| paramMiss
    (n : Name) 
    (k : Level)
    (v : Level)
    (l' : Level)
    (ks_tl : list Level)
    (vs_tl : list Level) :
    let l := Param n,
        ks := k :: ks_tl,
        vs := v :: vs_tl
    in
    -- ASSERT : Param n ≠ k
    subst l ks_tl vs_tl l'
    -> subst l ks vs l'


inductive substMany : ∀ (ls : list Level) (ks : list Level) (vs : list Level) (ls' : list Level), Prop
| base (ks vs : list Level) : 
    let ls : list Level := [],
        ls' : list Level := []
    in 
    substMany ls ks vs ls'

| step 
    (ls_hd : Level) 
    (ls_hd' : Level) 
    (ls_tl : list Level)
    (ls_tl' : list Level)
    (ks : list Level)
    (vs : list Level) :
    let ls := ls_hd :: ls_tl,
        ls' := ls_hd' :: ls_tl'
    in
    substMany ls_tl ks vs ls_tl' 
    -> subst ls_hd ks vs ls_hd' 
    -> substMany ls ks vs ls'


-- `false : bool` used both to mean ¬(L ≤ R) and that it can't
-- be determined whether or not L ≤ R
mutual inductive ensureImaxLeq, leqCore
-- If you get either (Imax _ (Param n) ≤ R) or (L ≤ Imax _ Param n),
-- check that ≤ holds if Param n is both zero and non-zero.
with ensureImaxLeq : 
    ∀ (i_snd : Level) 
      (l : Level) 
      (r : Level) 
      (l_h : nat) 
      (r_h : nat) 
      (result : bool), 
      Prop
| base 
    (i_snd : Level)
    (l : Level)
    (r : Level)
    (l_h : nat)
    (r_h : nat) 
    (l_z : Level)
    (r_z : Level)
    (l_z' : Level)
    (r_z' : Level)
    (l_s : Level)
    (r_s : Level)
    (l_s' : Level)
    (r_s' : Level)
    (b1 : bool)
    (b2 : bool) :
    let pp := [i_snd],
        zz := [Zero],
        s_pp := [Succ i_snd],
        result := b1 && b2
    in
    subst l pp zz l_z
    -> subst r pp zz r_z
    -> simplify l_z l_z'
    -> simplify r_z r_z'
    -> leqCore l_z' r_z' l_h r_h b1
    -> subst l pp s_pp l_s
    -> subst r pp s_pp r_s
    -> simplify l_s l_s'
    -> simplify r_s r_s'
    -> leqCore l_s' r_s' l_h r_h b2
    -> ensureImaxLeq i_snd l r l_h r_h result

with leqCore : ∀ (l : Level) (r : Level) (l_h : nat) (r_h : nat) (result : bool), Prop
| z_any 
    (r : Level) 
    (l_h : nat)
    (r_h : nat) : 
    let l := Zero,
        result := tt
    in
    -- ASSERT : l_h ≤ r_h
    leqCore l r l_h r_h result

| any_z 
    (l : Level) 
    (l_h : nat)
    (r_h : nat) : 
    let r := Zero,
        result := ff
    in
    -- ASSERT : r_h < l_h 
    leqCore l r l_h r_h result

| p_p 
    (n1 : Name)
    (n2 : Name) 
    (l_h : nat)
    (r_h : nat) : 
    let l := Param n1,
        r := Param n2,
        result := (n1 = n2) && (l_h ≤ r_h)
    in
    leqCore l r l_h r_h result

| p_z 
    (n : Name) 
    (l_h : nat)
    (r_h : nat) : 
    let l := Param n,
        r := Zero,
        result := ff
    in
    leqCore l r l_h r_h result

| z_p 
    (n : Name) 
    (l_h : nat)
    (r_h : nat) : 
    let l := Zero,
        r := Param n,
        result := l_h ≤ r_h
    in
    leqCore l r l_h r_h result

| s_any 
    (l_pred : Level) 
    (r : Level) 
    (l_h : nat)
    (r_h : nat) 
    (result : bool) :
    let l_h' := (1 + l_h),
        l := Succ l_pred
    in
    leqCore l_pred r l_h' r_h result
    -> leqCore l r l_h r_h result

| any_s 
    (l : Level)
    (r_pred : Level) 
    (l_h : nat)
    (r_h : nat) 
    (result : bool) :
    let r_h' := 1 + r_h,
        r := Succ r_pred
    in
    leqCore l r l_h r_h' result
    -> leqCore l r l_h r_h result

| max_any 
    (fst : Level)
    (snd  : Level)
    (r : Level) 
    (l_h : nat) 
    (r_h : nat) 
    (b1 : bool)
    (b2 : bool) :
    let l := Max fst snd,
        result := b1 && b2
    in
    leqCore fst r l_h r_h b1
    -> leqCore snd r l_h r_h b2
    -> leqCore l r l_h r_h result
            
| p_max 
    (n : Name)
    (fst  : Level)
    (snd : Level)
    (b1  : bool)
    (b2 : bool)
    (l_h : nat)
    (r_h : nat) :
    let l := Param n,
        r := Max fst snd,
        result := b1 || b2
    in
    leqCore (Param n) fst l_h r_h b1
    -> leqCore (Param n) snd l_h r_h b2
    -> leqCore (Param n) r l_h r_h result

| z_max 
    (fst : Level)
    (snd : Level)
    (b1 : bool)
    (b2 : bool)
    (l_h  : nat)
    (r_h : nat) :
    let l := Zero,
        r := Max fst snd,
        result := b1 || b2
    in
    leqCore l fst l_h r_h b1
    -> leqCore l snd l_h r_h b2
    -> leqCore l r l_h r_h result

| imim_congr 
    (fst : Level)
    (snd : Level) 
    (l_h : nat)
    (r_h : nat) : 
    let l := Imax fst snd,
        r := Imax fst snd,
        result := tt
    in
    leqCore l r l_h r_h result

| im_p_any 
    (n : Name)
    (fst : Level)
    (r : Level)
    (l_h : nat)
    (r_h : nat) 
    (result : bool) :
    let snd := Param n,
        l := Imax fst snd
    in
    ensureImaxLeq snd l r l_h r_h result
    -> leqCore l r l_h r_h result

| any_im_p 
    (n : Name)
    (fst : Level)
    (l : Level)
    (l_h : nat)
    (r_h : nat)
    (result : bool) :
    let snd := Param n,
        r := Imax fst snd
    in
    ensureImaxLeq snd l r l_h r_h result
    -> leqCore l r l_h r_h result


| imim_any 
    (a : Level) 
    (c : Level) 
    (d : Level) 
    (r : Level)
    (l_h : nat)
    (r_h : nat)
    (result : bool) :
    let l' := Max (Imax a d) (Imax c d),
        l := Imax a (Imax c d)
    in
    leqCore l' r l_h r_h result
    -> leqCore l r l_h r_h result

| imm_any 
    (a : Level)
    (c : Level) 
    (d : Level) 
    (r : Level) 
    (new_max' : Level)
    (l_h : nat)
    (r_h : nat)
    (b : bool) :
    let l' := Max (Imax a c) (Imax a d),
        l := Imax a (Max c d)
    in
    simplify l' new_max'
    -> leqCore new_max' r l_h r_h b
    -> leqCore l r l_h r_h b

| any_imim 
    (l : Level)
    (x : Level)
    (j : Level)
    (k : Level)
    (l_h : nat)
    (r_h : nat)
    (result : bool) :
    let r' := Max (Imax x k) (Imax j k),
        r := Imax x (Imax j k)
    in
    leqCore l r' l_h r_h result
    -> leqCore l r l_h r_h result

| any_imm 
    (l : Level)
    (x : Level) 
    (j : Level) 
    (k : Level) 
    (new_max' : Level)
    (l_h : nat)
    (r_h : nat)
    (result : bool) :
    let r' := Max (Imax x j) (Imax x k),
        r := Imax x (Max j k)
    in
    simplify (Max (Imax x j) (Imax x k)) new_max'
    -> leqCore l new_max' l_h r_h result
    -> leqCore l (Imax x (Max j k)) l_h r_h result

inductive leq : ∀ (l : Level) (r : Level) (b : bool), Prop
| mk
    (l : Level)
    (r : Level)
    (l' : Level)
    (r' : Level)
    (b : bool) :
    simplify l l'
    -> simplify r r'
    -> leqCore l' r' 0 0 b
    -> leq l r b

inductive eqAntisymm : ∀ (l : Level) (r : Level) (b : bool), Prop
| mk 
    (l : Level)
    (r : Level)
    (b1 : bool)
    (b2 : bool) :
    let result := b1 && b2
    in
    leq l r b1 
    -> leq r l b2 
    -> eqAntisymm l r result

inductive isZero : ∀ (l : Level) (b : bool), Prop
| mk (l : Level) (b : bool) : leq l Zero b -> isZero l b

inductive isNonzero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : leq (Succ Zero) l b -> isNonzero l b

inductive maybeZero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : isNonzero l b -> maybeZero l (¬b)

inductive maybeNonzero : Level -> bool -> Prop
| mk (l : Level) (b : bool) : isZero l b -> maybeNonzero l (¬b)

inductive eqAntisymmMany : list Level -> list Level -> bool -> Prop
| baseT : 
    let ls : list Level := [],
        rs : list Level := [],
        result := tt
    in eqAntisymmMany ls rs result
| baseFL (hd : Level) (tl : list Level) : 
    let ls := hd :: tl,
        rs : list Level := [],
        result := ff
    in
    eqAntisymmMany ls rs result

| baseFR (hd : Level) (tl : list Level) : 
    let ls : list Level := [],
        rs := hd :: tl,
        result := ff
    in
    eqAntisymmMany ls rs result
| step 
    (l_hd : Level)
    (r_hd : Level) 
    (l_tl : list Level)
    (r_tl : list Level)
    (b1 : bool)
    (b2 : bool) :
    let ls := l_hd :: l_tl,
        rs := r_hd :: r_tl,
        result := b1 && b2
    in
    eqAntisymm l_hd r_hd b1
    -> eqAntisymmMany l_tl r_tl b2
    -> eqAntisymmMany ls rs result

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
inductive foldImaxs : ∀ (ls : list Level) (l : Level) (result : Level), Prop
| base (l : Level) : 
    let ls : list Level := [],
        result := l
    in
    foldImaxs ls l result

| step 
    (hd : Level)
    (tl : list Level)
    (l : Level)
    (result : Level) :
    let ls := hd :: tl,
        combined := Imax hd l
    in
    foldImaxs tl combined result
    -> foldImaxs ls l result

end Level
