
import 
    .name 
    .level 
    .expr

open Expr


inductive Hint
| Opaq
| Reg (n : nat)
| Abbrev

instance : decidable_eq Hint := by tactic.mk_dec_eq_instance

open Hint

/-
Since we no longer output/track hints for delta reduction
for delta reduction, the stuff about ordering on hints is
just for the sake of completeness.
-/
inductive hintLe : Hint -> Hint -> Prop
| opaqLe (r : Hint) : hintLe Opaq r
| regLe (a b : nat) : a ≤ b -> hintLe (Reg a) (Reg b)
| leAbbrev (h : Hint) : hintLe h Abbrev

instance hint_has_le : has_le Hint := ⟨ hintLe ⟩
instance hint_has_lt : has_lt Hint := ⟨ λ h1 h2, (h1 ≤ h2) ∧ ¬(h2 ≤ h1) ⟩ 

structure RecRule :=
(ctor_name : Name)
(num_fields : nat)
(val : Expr)

instance : decidable_eq RecRule := by tactic.mk_dec_eq_instance

inductive Declar
| Axiom 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (is_unsafe : bool) :
    Declar

| Definition 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (val : Expr)
    (hint : Hint)
    (is_unsafe : bool) :
    Declar

| Theorem
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (val : Expr) :
    Declar

| Opaque
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (val : Expr)
    (is_unsafe : bool) :
    Declar

| Quot 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr) :
    Declar

| Inductive 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (num_params : nat)
    (all_ind_names : list Name)
    (all_ctor_names : list Name)
    (is_unsafe : bool) :
    Declar

| Constructor 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (parent_name : Name)
    (num_fields : nat)
    (num_params : nat)
    (is_unsafe : bool) :
    Declar

| Recursor 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (all_names : list Name)
    (num_params : nat)
    (num_indices : nat)
    (num_motives : nat)
    (num_minors : nat)
    (major_idx : nat)
    (rec_rules : list RecRule)
    (is_k : bool)
    (is_unsafe : bool) :
    Declar


instance : decidable_eq Declar := by tactic.mk_dec_eq_instance

structure DeclarView :=
(name : Name)
(uparams : list Level)
(type_ : Expr)
(val : option Expr)

namespace Declar

/-
The way I chose to do this wrt the output file is that every time
a `Declar` gets created and introduced in the trace, the next line
introduces a `DeclarView` item which has the same element number
(though a different suffix so they can be properly parsed).
-/
def mkDeclarView : Declar -> DeclarView
| (Axiom n ups t _) := ⟨n, ups, t, none⟩
| (Definition n ups t v _ _) := ⟨n, ups, t, some v⟩ 
| (Theorem n ups t v ) := ⟨n, ups, t, some v⟩ 
| (Opaque n ups t v _) := ⟨n, ups, t, some v⟩ 
| (Quot n ups t) := ⟨n, ups, t, none⟩
| (Inductive n ups t _ _ _ _) := ⟨n, ups, t, none⟩
| (Constructor n ups t _ _ _ _) := ⟨n, ups, t, none⟩
| (Recursor n ups t _ _ _ _ _ _ _ _ _) := ⟨n, ups, t, none⟩

-- Just a helper function for turning declar into (declar.name, declar)
-- so we can insert things into the environment list more easily.
def asKvPair (d : Declar) : (Name × Declar) := (d.mkDeclarView.1, d)

end Declar


@[reducible]
def Env := list (Name × Declar)


namespace Env

-- shows up as a 3-tuple (nameRef, nat, declarRef)
-- where the nat is a stepRef pointing to the AdmitDeclar step.
inductive getDeclar : Name -> Env -> Declar -> Prop

-- shows up as a 3-tuple (nameRef, nat, declarViewRef)
-- where the nat is a stepRef pointing to the AdmitDeclar step.
inductive getDeclarView : Name -> Env -> DeclarView -> Prop

-- Kind of a pain in the ass that we even need this, but retrieving
-- the corresponding RecRule is the only place where we need
-- to get a list element based on a predicate.
-- In the context of a proof printer, this will always succeed,
inductive getRecRule : 
    ∀ (rec_rules : list RecRule) 
      (major_name : Name) 
      (rec_rule : RecRule), 
      Prop
| base 
    (major_name : Name)
    (num_fields : nat)
    (val : Expr)
    (rrs_tl : list RecRule) :
    let rec_rule := RecRule.mk major_name num_fields val,
        rrs := (rec_rule :: rrs_tl)
    in
    getRecRule rrs major_name rec_rule

| step 
    (ctor_name : Name)
    (num_fields : nat)
    (val : Expr)
    (rrs_tl : list RecRule)
    (major_name : Name) 
    (out : RecRule) :
    let x := RecRule.mk ctor_name num_fields val,
        rec_rules := (x :: rrs_tl)
    in
    -- ASSERT : ctor_name ≠ major_name
    getRecRule rrs_tl major_name out
    -> getRecRule rec_rules major_name out

    

end Env

