
import 
    .name 
    .level 
    .expr

open Expr

inductive Hint
| Opaq
| Reg (n : nat)
| Abbrev


open Hint

inductive hintLe : Hint -> Hint -> Prop
| base (r : Hint) : hintLe Opaq r
| regLe (a b : nat) : a ≤ b -> hintLe (Reg a) (Reg b)
| rest (h : Hint) : hintLe h Abbrev


instance hint_has_le : has_le Hint := ⟨ hintLe ⟩

instance hint_has_lt : has_lt Hint := ⟨ λ h1 h2, (h1 ≤ h2) ∧ ¬(h2 ≤ h1) ⟩ 


instance : decidable_eq Hint := by tactic.mk_dec_eq_instance

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
    (is_unsafe : bool) 
    : Declar

| Definition 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (val : Expr)
    (hint : Hint)
    (is_unsafe : bool) 
    : Declar

| Quot 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr) 
    : Declar

| Inductive 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (num_params : nat)
    (all_ind_names : list Name)
    (all_ctor_names : list Name)
    (is_unsafe : bool) 
    : Declar

| Constructor 
    (name : Name)
    (uparams : list Level)
    (type_ : Expr)
    (parent_name : Name)
    (num_fields : nat)
    (minor_idx : nat)
    (num_params : nat)
    (is_unsafe : bool) 
    : Declar

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
    (is_unsafe : bool) 
    : Declar

instance : decidable_eq Declar := by tactic.mk_dec_eq_instance

inductive declarVitals (d : Declar) (n : Name) (ups : list Level) (t : Expr) : Prop 

inductive getDeclarName : Declar -> Name -> Prop
inductive getDeclarUparams : Declar -> list Level -> Prop
inductive getDeclarType : Declar -> Expr -> Prop

open Hint Declar
namespace Declar

end Declar

@[reducible]
def Env := list (Name × Declar)


namespace Env

inductive getDeclar : Env -> Name -> Declar -> Prop

-- this should always succeed (in the context of a proof
-- printer) so has no `nil` case and does not return an option.
inductive getRecRuleAux : list RecRule -> Name -> RecRule -> Prop
| base 
    (major_name : Name)
    (num_fields : nat)
    (val : Expr)
    (rest : list RecRule)
    : let rr := RecRule.mk major_name num_fields val
    in
    getRecRuleAux (rr :: rest) major_name rr

| step 
    (ctor_name : Name)
    (num_fields : nat)
    (val : Expr)
    (rest : list RecRule)
    (major_name : Name)
    (rr : RecRule)
    : ctor_name ≠ major_name
    -> getRecRuleAux rest major_name rr
    -> getRecRuleAux ((RecRule.mk ctor_name num_fields val) :: rest) major_name rr

inductive getRecRule : list RecRule -> Expr -> RecRule -> Prop
| base 
    (rrs : list RecRule)
    (major : Expr)
    (major_name : Name)
    (major_levels : list Level)
    (major_args : list Expr)
    (rr : RecRule)
    : unfoldApps major (mkConst major_name major_levels) major_args
    -> getRecRuleAux rrs major_name rr
    -> getRecRule rrs major rr

    
    

end Env

