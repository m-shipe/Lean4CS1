/- @@@

# Notes 9/21/26


- Curry-Howard Injection: Deductive Reasoning (Prop) => Computation (Type)

- Deep vs Shallow embedding of abstract theories into Lean 4
  - Deep embedding: Syntax as a type with constructor for each kind of term (propositional logic)
  - Shallow embedding: Syntax as collection of types, one for each kind of term (predicate logic)

  - Empty and False
  - Unit and True
  - Prod and And
  - Sum and Or
  -


@@@ -/

inductive proplogicsyntax where
| T
| F
| And (left right : proplogicsyntax)
| Or (left right : proplogicsyntax)
| Not (p : proplogicsyntax)

namespace proplogicsyntax

def eval : proplogicsyntax → Bool
  | T => true
  | F => false
  | And left right => eval left && eval right
  | Or left right => eval left || eval right
  | Not p => !eval p

end proplogicsyntax

inductive proplogicstheory where
| axiom (p : proplogicsyntax)
| and_intro (p q : proplogicsyntax) (hp : proplogicstheory) (hq : proplogicstheory) : proplogicstheory
| and_elim_left (p q : proplogicsyntax) (h : proplogicstheory) : proplogicstheory
| and_elim_right (p q : proplogicsyntax) (h : proplogicstheory) : proplogicstheory
| or_intro_left (p q : proplogicsyntax) (h : proplogicstheory) : proplogicstheory
| or_intro_right (p q : proplogicsyntax) (h : proplogicstheory) : proplogicstheory
| or_elim (p q r : proplogicsyntax) (h1 : proplogicstheory) (h2 : proplogicstheory) : proplogicstheory
| not_intro (p : proplogicsyntax) (h : proplogicstheory) : proplogicstheory
| not_elim (p : proplogicsyntax) (h1 : proplogicstheory) (h2 : proplogicstheory) : proplogicstheory
| implies_intro (p q : proplogicsyntax) (h : proplogicstheory) : proplogicstheory

#check proplogicstheory.axiom proplogicsyntax.F

#eval proplogicsyntax.eval (proplogicsyntax.And proplogicsyntax.T
  (proplogicsyntax.Not proplogicsyntax.F))

inductive MyEmpty : Prop where

def myEmptyToEmpty : MyEmpty → Empty := fun value => nomatch value

inductive MyTrue : Prop where
| intro

theorem myTrue : MyTrue → True := fun _ => True.intro

def neg (α : Prop) : Prop := α → False

theorem not_negMyTrue : ¬ neg MyTrue := by
  intro h
  exact h MyTrue.intro

inductive kifcville : Prop where
| driverslicense

inductive jiftoronto: Prop where
| driverslicense
| utilitybill
| healthcard

example : kifcville := kifcville.driverslicense

example : And jiftoronto kifcville := And.intro jiftoronto.utilitybill kifcville.driverslicense

theorem not_and_eval (P Q : proplogicsyntax) :
    ¬(proplogicsyntax.eval P = true ∧ proplogicsyntax.eval Q = true) →
      proplogicsyntax.eval P ≠ true ∨ proplogicsyntax.eval Q ≠ true := by
  intro h
  by_cases hP : proplogicsyntax.eval P = true
  · by_cases hQ : proplogicsyntax.eval Q = true
    · exfalso
      apply h
      apply And.intro
      · exact hP
      · exact hQ
    · right
      exact hQ
  · left
    exact hP

theorem DM1 : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
  by
    intro P Q h
    by_cases hP : P
    · right
      intro hQ
      exact h ⟨hP, hQ⟩
    · left
      exact hP

theorem DM2 : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun P _Q => -- ∀ intro (twice)
  fun h => -- ∀ intro
  fun pandq => -- → intro
  let p : P := And.left pandq -- And.elim on left
  let q := pandq.right -- And.elim on right
  match h with -- Or elim (by cases)

  | Or.inl np => np p -- → elim (fn application)

  | Or.inr nq => nq q -- → elim (fn application)

/- @@@

Mandatory homework: State and prove the two remaining

variants of DeMorgan's laws, involving distribution of

negation over disjunction (not over or).

@@@ -/

theorem DM3 : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun _ _ pandq =>
    And.intro
      (fun P => pandq (Or.inl P))
      (fun Q => pandq (Or.inr Q))

theorem DM4 : ∀ (P Q : Prop), ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun _ _ h porq =>
    match porq with
    | Or.inl P => h.left P
    | Or.inr Q => h.right Q

example (P Q : Prop) (em : ∀ (X : Prop), X ∨ ¬X) : ¬(P ∧ Q) → (¬P ∨ ¬Q) :=
  fun h =>
    match em P with
    | Or.inl p => Or.inr (fun q => h (And.intro p q))
    | Or.inr np => Or.inl np



#check ∀ P : Prop, ¬(P ∧ ¬P)
theorem andnot (P : Prop) : (P ∧ ¬P) → False :=
  fun h => h.2 h.1

theorem not_andnot (P : Prop) : ¬(P ∧ ¬P) → True :=
  fun _ => True.intro

def fact : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * fact n

def fibo : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 =>  fibo (n+1) + fibo (n)

#eval fact 2

/- @@@
# A Language of Arithmetic, in Lean
@@@ -/


namespace Arith

/- @@@
## Syntax
@@@ -/

inductive Var where
| mk (index : Nat) : Var
open Var

def varInterp : Var → Nat
| Var.mk 0 => 6
| Var.mk 1 => 2
| Var.mk 2 => 11
| Var.mk 3 => 1
| Var.mk _ => 0

inductive ArithExpr where
| lit (n : Nat) : ArithExpr
| add (e1 e2 : ArithExpr) : ArithExpr
| inc (e1 : ArithExpr) : ArithExpr
| mul (e1 e2 : ArithExpr) : ArithExpr
| exp (e1 e2 : ArithExpr) : ArithExpr
| tet (e1 e2 : ArithExpr) : ArithExpr
| var (v : Var) : ArithExpr
open ArithExpr

-- examples expressions using our syntax
def e1 : ArithExpr := lit 1
def e7 : ArithExpr := lit 7
def e3 : ArithExpr := add e1 e7
def e4 : ArithExpr :=   -- 7 + (6 + 9)
  add
    (lit 7)
    (add
      (lit 6)
      (lit 9)
    )


/-@@@
# Operational Semantics
@@@ -/
def tetration : Nat → Nat → Nat
| _, 0 => 1
| n, 1 => n
| n1, n2 + 2 => n1 ^ tetration n1 (n2 + 1)

def arithEval (interp : Var → Nat) : ArithExpr → Nat
| lit n => n
| add e1 e2 => (arithEval interp e1) + (arithEval interp e2)
| inc e1 => (arithEval interp e1) + 1
| mul e1 e2 => (arithEval interp e1) * (arithEval interp e2)
| exp e1 e2 => (arithEval interp e1) ^ (arithEval interp e2)
| tet e1 e2 => tetration (arithEval interp e1) (arithEval interp e2)
| var v => interp v

-- and here's what it means: 22
def e2 := lit 2
def e5 := lit 5
#eval arithEval varInterp e4
#eval arithEval varInterp (inc e4)
#eval arithEval varInterp (mul e7 e3)
#eval arithEval varInterp (exp e7 e3)
#eval arithEval varInterp (tet e5 e2)



/- @@@
## To Prepare For Next Class

To be prepared to participate in the
conversation in next class, which I do
strongly recommend to you all, please
do the following before next class.

(1) add support for the following forms
- inc (n : Nat)   -- will mean *add 1*
- mul (n m : Nat) -- will mean n * m
- exp (n m : Nat) -- will mean n ^ m
- tet (n m : Nat) -- n^n^n... m times
- var (v : Var)   -- needs *interpretation*

(2) To handle `var` you will need
to add a `Var` type. Go study how
we did this for variable exprssions
in propositional logic. It's okay,
as in that code, to define a Var
type with just a few instances, such
as X, Y, Z, and W (four constructors
with these names) A better design is
one with a single Var constructor that
takes a Nat "index" to distinguish one
variable from another. Then you can do
this: `def X := Var.mk 0`, then define
`Y := Var.mk 1`, and so forth. You'll
then have a `Var` type supporting an
infinite set of variables, *indexed by
natural numbers*, and you can bind nice
names to any finite number of them you
plan to use in a given application. An
*interpretation* is then a function from
Nat-indexed variable objects to Nat values.
NB: The index is *not* the value of the
variable, it's what makes one variable
distinct from another. Again, you will
define a separate interpretation function
to model the binding of these `Var` objects
to different Nat values.

It will look something like this:

```lean
define varInterp : Var → Nat
| Var.mk 0 => 6   -- evaluate X (Var 0) to 6
| Var.mk 1 => 2   -- evaluate Y to 2
| Var.mk 2 => 11  -- evaluate Z to 11
| Var.mk 3 => 1   -- evaluate W to 1
| Var.mk _ => 0   -- otherwise 0
```

Note that you need that last case to
make the varInterp function total, as
there is now an infinitude of distinct
`Var` values.

Then just as we did with propositional
logic as we embedded it in Lean, you'll
need to update the `arithEval` semantic
evaluator to take not only an expression
but also a variable interpretation as its
arguments. Evaluating an arithmetic expr
then produces different answers in general
for different interpretations. To be very
concrete about it, evaluating *X + Y* under
an interpretation, *{ X => 1, Y => 2}* will
in general produce different value under
different interpretations. Here it's 3, but
evaluating *X + Y* under *{ X => 3, Y => 2}*
will give *5* as its meaning under this new
interpretation.
@@@ -/

end Arith
