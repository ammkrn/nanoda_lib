import 
    .name
    .level
    .expr
    .env
    .tc

/-
Todo

open Name Level Expr Declar

inductive checkIndType : Expr -> Prop
inductive checkCtor : Expr -> Prop

inductive mkLocalParams : nat -> Expr -> list Expr -> Prop
| base (e : Expr) : mkLocalParams 0 e []
| step 
    (rem_params : nat)
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b' : Expr)
    (sink : list Expr)
    : let local_param := mkLocal n t s serial
    in
    inst1 b local_param b'
    -> mkLocalParams (rem_params - 1) b' sink
    -> mkLocalParams rem_params (mkPi n t s b) (local_param :: sink)

-- ind_type, local_params, local_indices
inductive mkLocalIndices1 : Expr -> list Expr -> list Expr -> Prop
| base (e : Expr) : isPi e ff -> mkLocalIndices1 e [] []
| stepIndex 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (serial : nat)
    (b' : Expr)
    (local_indices : list Expr)
    : let local_index := mkLocal n t s serial
    in
    inst1 b local_index b'
    -> mkLocalIndices1 b' [] local_indices
    -> mkLocalIndices1 (mkPi n t s b) [] (local_index :: local_indices)

| stepParam 
    (n : Name)
    (t : Expr)
    (s : Bstyle)
    (b : Expr)
    (b' : Expr)
    (local_param : Expr)
    (local_params : list Expr)
    (local_indices : list Expr)
    : inst1 b local_param b'
    -> mkLocalIndices1 b' local_params local_indices
    -> mkLocalIndices1 (mkPi n t s b) (local_param :: local_params) local_indices
            
            


-- ind_types -> local_params -> flat local indices
--inductive mkLocalIndicesAux : list Expr -> list Expr -> list Expr -> Prop
--| base (local_params : list Expr) : mkLocalIndicesAux [] local_params []
--| step (ind_type : Expr)
--       (ind_types : list Expr)
--       (local_params : list Expr)
-/
