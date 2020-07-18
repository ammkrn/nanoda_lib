variable {A : Type}
variable [decidable_eq A]

open nat list

/-
Stand-in for uses of `get` (AKA `nth`) in which the list
is guaranteed to be of at least length (n + 1), meaning
it will never fail or return `None`, so we can skip the option type.
Since we're not proving theorems we just define this as a `sorry`
and use it to define relationships between elements in let bindings.
-/
def getInfal : list A -> nat -> A := sorry

inductive listPos (needle : A) : ∀ (haystack : list A) (pos : option nat), Prop
| baseNone : 
    let haystack : list A := [],
        pos : option nat := none
    in listPos haystack pos
| baseSome (haystack_tl : list A) :
    let haystack := (needle :: haystack_tl),
        pos := some 0
    in listPos haystack pos
| step 
    (x : A)
    (haystack_tl : list A) 
    (pos : option nat) :
    let haystack := (x :: haystack_tl),
        pos' := succ <$> pos
    in 
    -- ASSERT : needle ≠ x
    listPos haystack_tl pos
    -> listPos haystack pos'

inductive listSubset : ∀ (sub super : list A) (result : bool), Prop
| base (super : list A) : 
    let sub : list A := [],
        result := tt 
    in listSubset sub super result
| step 
    (hd : A) 
    (maybe_pos : option nat)
    (sub : list A)
    (super : list A) 
    (result : bool) :
    let sub' := hd :: sub,
        result' := maybe_pos.is_some && result
    in
    listPos hd super maybe_pos
    -> listSubset sub super result
    -> listSubset sub' super result'

-- assesrtion-like; no false case
inductive listNoDupes : ∀ (l : list A), Prop
| baseNil : let l : list A := [] in listNoDupes l
| step (hd : A) (tl : list A)  :
    let l := (hd :: tl)
    in 
    listPos hd tl none
    -> listNoDupes tl
    -> listNoDupes l

