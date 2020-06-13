
--@[derive decidable_eq]
inductive Name
| Anon : Name
| Str (pfx : Name) (sfx : string) : Name
| Num (pfx : Name) (sfx : nat) : Name


instance : decidable_eq Name := by tactic.mk_dec_eq_instance

namespace Name

inductive getPrefix : Name -> Name -> Prop
| baseAnon : getPrefix Anon Anon
| stepStr (pfx : Name) (s : string) : getPrefix (Str pfx s) pfx
| stepNum (pfx : Name) (n : nat) : getPrefix (Num pfx n) pfx

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



