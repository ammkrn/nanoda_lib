/-
The type of names; works like a regular `list` type
but with two constructors, and it grows from left to right 
instead of right to left.
Initial element is `Anon`, the empty name; can tack on either
a string or a natural number with each constructor application.
-/

inductive Name
| Anon : Name
| Str (pfx : Name) (sfx : string) : Name
| Num (pfx : Name) (sfx : nat) : Name


instance : decidable_eq Name := by tactic.mk_dec_eq_instance

namespace Name

inductive getPrefix : ∀ (n : Name) (pfx : Name), Prop
| baseAnon : 
    let n := Anon,
        pfx := Anon
    in getPrefix n pfx
| stepStr (pfx : Name) (sfx : string) : 
    let n := (Str pfx sfx)
    in getPrefix n pfx
| stepNum (pfx : Name) (sfx : nat) : 
    let n := (Num pfx sfx)
    in getPrefix n pfx

def dbg : Name → string
| Anon := ""
| (Str Anon sfx) := sfx
| (Num Anon sfx) := repr sfx
| (Str pfx sfx) := dbg pfx ++ "." ++ sfx 
| (Num pfx sfx) := dbg pfx ++ "." ++ repr sfx

instance : has_repr Name := ⟨dbg⟩ 

end Name

open Name
def n1 := Str (Num (Str (Str Anon "A") "B") 1) "C"
def n2 := Str (Num (Str (Num Anon 3) "B") 1) "C"



