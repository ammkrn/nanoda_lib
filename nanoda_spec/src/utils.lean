variable {A : Type}
variable [decidable_eq A]

open nat list

inductive trySucc : option nat -> option nat -> Prop
| baseNone : trySucc none none
| stepNat (n : ℕ) : trySucc (some n) (some $ succ n)


inductive listMem : A -> list A -> bool -> Prop
| baseFf (needle : A) : listMem needle [] ff
| baseTt (needle : A) (tl : list A) : listMem needle (needle :: tl) tt
| step (needle x : A) 
       (tl : list A) 
       (bl : bool) 
       : listMem needle tl bl
         -> listMem needle (x :: tl) ((needle = x) || bl)


inductive listPos : A -> list A -> option nat -> Prop
| baseNone (needle : A) : listPos needle [] none
| baseSome (needle : A) (tl : list A) : listPos needle (needle :: tl) (some 0)
| step (needle x : A) 
       (tl : list A) 
       (n n' : option nat) 
       : listPos needle tl n
         -> trySucc n n'
         -> listPos needle (x :: tl) n'

inductive listSubset : list A -> list A -> bool -> Prop
| base (super : list A) : listSubset [] super tt
| step (hd : A) 
       (sub super : list A) 
       (b1 b2 : bool) 
       : listMem hd super b2
         -> listSubset sub super b1 
         -> listSubset (hd :: sub) super (b1 && b2)

inductive listSkip : list A -> nat -> list A -> Prop
| baseNil (n : nat) : listSkip [] n []
| baseZero (l : list A) : listSkip l 0 l
| step (hd : A) 
       (tl l' : list A) 
       (n' : nat) 
       : listSkip (tl) n' l'
         -> listSkip (hd :: tl) (succ n') l'

inductive listTake : list A -> nat -> list A -> Prop
| baseNil (n : nat) : listTake [] n []
| baseZero (l : list A) : listTake l 0 []
| step (hd : A) 
       (tl l' : list A)
       (n' : nat) 
       : listTake tl n' l'
         -> listTake (hd :: tl) (succ n') (hd :: l')

inductive listNoDupes : list A -> bool -> Prop
| baseNil : listNoDupes [] tt
| step (hd : A) (tl : list A) (b1 b2 : bool) : listMem hd tl b1
                                            -> listNoDupes tl b2
                                            -> listNoDupes (hd :: tl) ((bnot b1) && b2)


inductive listGet : list A -> nat -> option A -> Prop
| baseNil (n : nat) : listGet [] n none
| baseZero (hd : A) (tl : list A) : listGet (hd :: tl) 0 (some hd)
| step (hd : A) 
       (tl : list A) 
       (n' : nat)
       (out : option A) 
       : listGet tl n' out
         -> listGet (hd :: tl) (succ n') out

inductive listLen : list A -> nat -> Prop
| baseNil : listLen [] 0
| step (hd : A) (tl : list A) (n : nat) : listLen tl n -> listLen (hd :: tl) (succ n)

inductive listConcat : list A -> list A -> list A -> Prop
| base (l2 : list A) : listConcat [] l2 l2
| step (hd : A) (tl l2 l2' : list A) : listConcat tl l2 l2'
                                       -> listConcat (hd :: tl) l2 (hd :: l2')

