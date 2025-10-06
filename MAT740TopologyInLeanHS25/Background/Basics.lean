import Mathlib.Tactic

/- **Welcome to MAT740 Topology in Lean!**

This file summarizes the basic features you will need to start
proving theorems in Lean 4. For more detail see

Mathematics in Lean:
https://leanprover-community.github.io/mathematics_in_lean/index.html

Theorem Proving in Lean:
https://leanprover.github.io/theorem_proving_in_lean4/

When you open this file in VS Code, you should see messages in the
"Lean InfoView" tab on the right side of the screen. -/

-- # Defining and evaluating expressions

-- You can define constants using the `def` keyword.
def myNumber : ℕ := 42

/- Here `myNumber` is the name of the constant.
The colon `:` indicates the type of `myNumber`, which in this case is `ℕ` (\N).
You should read 'myNumber has type ℕ'.
You can imagine types to be like sets, and `:` like `∈`.
You can get unicode characters by typing `\` and their name.
The `:=` is used to indicate an equality that holds by definition. -/

-- Functions are also defined using `def`.
def myAddition (x y : ℕ) : ℕ := x + y

/- The arguments of the function are written after the name.
Their types are also annotated.
You should think of `myAddition x y` as a unit
and read 'myAddition x y has type ℕ'. -/

-- You can print the definition of an expression using `#print`.
#print myNumber
#print myAddition

-- You can check the type of an expression using `#check`.
#check myNumber        -- Outputs: ℕ
#check myAddition      -- Outputs: ℕ → ℕ → ℕ

-- You can evaluate expressions using `#eval`.
#eval myNumber          -- Outputs: 42
#eval myAddition 3 5   -- Outputs: 8

-- Anonymous functions can be defined using the `fun` keyword
def myAddition' : ℕ → ℕ → ℕ := fun (x y : ℕ) => x + y

/- The arrow `→` (\to) indicates a function type.
In Lean, all functions have a single argument.
Multi-argument functions can be produced by 'currying':
`myAddition'` takes `(x₀ : ℕ)` and returns a function `myAddition x₀ : ℕ → ℕ` which sends `y ↦ x₀ + y`.
Think `x ↦ (y ↦ x + y)`.
The brackets for `→` associate to the right so that
`ℕ → ℕ → ℕ` equals `ℕ → (ℕ → ℕ)` -/

-- You can use `let` for local definitions (e.g. inside functions)
def mulSquare (x y : ℝ) : ℝ :=
  let y2 := y*y
  x * y2

/- # Proving theorems
Lean is based on dependent type theory. This allows for the construction of very expressive types.

For example:
- f : ℕ → ℝ (function types)
- x : ℕ × ℝ (product types)
- w : a = b (equality types)

In particular, types are themselves types:
- ℕ : Type
- Type : Type 1

Types are allowed to depend on other types.
For example, for every `α : Type` there is a type `List α` of lists with elements of type `α`.

This allows us to write functions where later arguments depend on earlier ones. -/
def singleton (α : Type) (x : α) : List α := [x]

#eval singleton ℕ 42

-- Lean can infer types, so we can leave `α` implicit by using `{}`.
def singleton' {α : Type} (x : α) : List α := [x]

#eval singleton' 42

/- ## Propositions as types
Leans type system is expressive enough to encode mathematical statements.

Mathematical statements have type `Prop` -/

#check (∀ n : ℕ, n = n)

/- Given a statement `S : Prop`, we think of a term `p : S` as a proof of `S`.
If `S` is inhabited, we think of it as true. Otherwise, `S` is false.

Thus to prove a statement `S : Prop`, we need to construct a proof `p : S`. -/

def p : ∀ n : ℕ, n = n :=
  fun n : ℕ => rfl --`rfl` is a distinguished element of `n = n`.

-- Lean provides a special `theorem` keyword for proofs.
theorem n_eq_n : ∀ n : ℕ, n = n :=
  fun n : ℕ => rfl

/- Like functions, theorems can depend on arguments.
We could have also written the above as.
Compare this to the two versions of `myAddition`. -/
theorem n_eq_n' (n : ℕ) : n = n :=
  rfl

-- There is also `example` if you don't want to name your theorem.
example (n : ℕ) : n = n :=
  rfl


/- ## Tactics
We will generally prove theorems using tactics.
Tactics mode is activates using `by`.

These are procedures that tell lean how to construct a proof term.
As such they allow for a large degree of automation. -/

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm] -- rewrite using an existing theorem

example (a b : ℕ) : a + b = b + a := by
  apply add_comm -- apply an existing theorem

example (a b : ℕ) : a + b = b + a := by
  ring -- automatically prove result from commutative ring axioms

/- For a guided introduction to proofs using tactics, see

Natural Number Game:
https://adam.math.hhu.de/#/g/leanprover-community/nng4

In the game, you can switch to writing the Lean code directly by
clicking the `</>` button in the top right corner.

The next file `1_Tactics.lean` provides an introduction to the most important tactics. -/
