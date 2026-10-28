

#check ∀ P : Prop, ¬(P ∧ ¬P)

theorem andnot (P : Prop) : (P ∧ ¬P) → False :=
  fun h => h.2 h.1

theorem not_andnot (P : Prop) : ¬(P ∧ ¬P) → True :=
  fun _ => True.intro

inductive Dog : Type where
| Fido
| Iris
| Seargent

open Dog

def isFurry : Dog → Prop
| _ => True

def isFriendly : Dog → Prop
| Dog.Seargent => False
| _ => True

inductive Friendly : Dog → Prop where
| dogfr (d : Dog) : isFriendly d → Friendly d

inductive Furry : Dog → Prop where
| dogfr (d : Dog) : isFurry d → Furry d

example : Friendly Iris ∨ Friendly Seargent := Or.inl (Friendly.dogfr Iris True.intro)

theorem notFriendlySeargent : ¬Friendly Seargent :=
  fun h => nomatch h

def Suitable (d : Dog) : Prop := (Friendly d ∧ Furry d)

example : Suitable Iris := And.intro (Friendly.dogfr Iris True.intro) (Furry.dogfr Iris True.intro)

#check (Suitable)
#check (Furry)
#check (Friendly)

example : ∃ (d : Dog), ¬Friendly d := Exists.intro Seargent notFriendlySeargent
example : ∃ (d : Dog), Friendly d := Exists.intro Fido (Friendly.dogfr Fido True.intro)

example : ¬(∀ (d : Dog), Friendly d) := fun allfriendly => nomatch allfriendly Seargent
