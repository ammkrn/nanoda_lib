
import .name 
       .level 
       .expr

open Expr

inductive Hint
| Opaq
| Reg (n : nat)
| Abbrev

instance : decidable_eq Hint := by tactic.mk_dec_eq_instance

structure RecRule :=
(ctor_name : Name)
(num_fields : nat)
(val : Expr)

instance : decidable_eq RecRule := by tactic.mk_dec_eq_instance

inductive Declar
| Axiom (name : Name)
        (uparams : list Level)
        (type_ : Expr)
        (is_unsafe : bool) 
        : Declar

| Definition (name : Name)
             (uparams : list Level)
             (type_ : Expr)
             (val : Expr)
             (hint : Hint)
             (is_unsafe : bool) 
             : Declar

| Quot (name : Name)
       (uparams : list Level)
       (type_ : Expr) 
       : Declar

| Inductive (name : Name)
            (uparams : list Level)
            (type_ : Expr)
            (num_params : nat)
            (all_ind_names : list Name)
            (all_ctor_names : list Name)
            (is_usnafe : bool) 
            : Declar

| Constructor (name : Name)
              (uparams : list Level)
              (type_ : Expr)
              (parent_name : Name)
              (num_fields : nat)
              (minor_idx : nat)
              (num_params : nat)
              (is_unsafe : bool) 
              : Declar

| Recursor (name : Name)
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

open Hint Declar
namespace Declar

end Declar

@[reducible]
def Env := list (Name × Declar)


namespace Env

end Env

