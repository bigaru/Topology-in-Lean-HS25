import Mathlib.Tactic

def myNumber : ℕ := 42

#print myNumber
#eval myNumber
#check myNumber

def myAddition (x y : ℕ) : ℕ := x + y

#eval myAddition 3 4

#check fun (x y : ℕ) ↦ x + y

def myAddition' : ℕ → ℕ → ℕ := fun (x y : ℕ) ↦ x + y
/-
In Lean all function have a single argument.
Multi-argument functions are obtained by currying:
E.g. myAddtion' `x₀ ↦ (y ↦ x₀ + y)`.
-/

def mulSquare (x y : ℕ) : ℕ :=
  let y2 := y * y
  x * y2

#eval mulSquare 2 3

/- # Proving theorems

Lean is based on dependent type theory. This allows you to build very expressive types.

For example:
- f : ℕ → ℝ
- x : ℕ × ℝ
- w : a = b

In particular, types are themselves type.
- ℕ : Type
- Type : Type 1

Moverover, type can depend on types.

For every type `α : Type` there is a type `List α`.
-/

def singleton (α : Type) (x : α) : List α := [x]

#eval singleton ℕ 3

def singleton' {α : Type} (x : α) : List α := [x]

#eval singleton' 3

/- # Proposition as type

Mathematical statements have type `Prop`.
-/

#check (∀ n : ℕ, n = n)

/- Given a statement `S : Prop`, we think of a term `p : S` as a proof of `S`.

If `S` is inhabited, we think of it as true, otherwise we think of it as false.

Hence to prove `S`, we need to construct a proof `p : S`.
-/

def p : ∀ n : ℕ, n = n :=
  fun n : ℕ => rfl

-- Lean provides special keywords for proofs.
theorem n_eq_n : ∀ n : ℕ, n = n :=
  fun n : ℕ => rfl

theorem n_eq_n' (n : ℕ) : n = n :=
  rfl

example : ∀ n : ℕ, n = n :=
  fun n : ℕ => rfl

/- # Tactics

We will generally be using tactics to prove theorems.

Tactics are instructions we provide to Lean on how to find a proof.
-/

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  apply add_comm

example (a b : ℕ) : a + b = b + a := by
  ring -- automatically proves identities in commutative rings
