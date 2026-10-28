import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | (n+1) => (n+1) * factorial n

def doublefact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | (n+2) => (n+2) * doublefact n

def triplefact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | (n+3) => (n+3) * triplefact n

#eval factorial 6
#eval doublefact 6
#eval triplefact 6

def identity (α : Type) (x : α) : α := x

#eval factorial (doublefact (triplefact 5))
