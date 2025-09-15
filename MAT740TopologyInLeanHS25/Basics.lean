import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- Welcome to MAT740 Topology in Lean!

This file summarizes the basic features you will need to start
proving theorems in Lean 4. For more detail see

Mathematics in Lean:
https://leanprover-community.github.io/mathematics_in_lean/index.html

When you open this file in VS Code, you should see messages in the
"Lean InfoView" tab on the right side of the screen.
-/

-- Defining and evaluating expressions --

-- You can define constants and functions using the `def` keyword.
def myNumber : Nat := 42
def myAddition (x y : Nat) : Nat := x + y

-- You can print the definition of an expression using the `#print` command.
#print myNumber
#print myAddition

-- You can check the type of an expression using the `#check` command.
#check myNumber        -- Outputs: Nat
#check myAddition      -- Outputs: Nat → Nat → Nat

-- You can evaluate expressions using the `#eval` command.
#eval myNumber          -- Outputs: 42
#eval myAddition 3 5   -- Outputs: 8

/- Proving theorems

We will generally prove theorems using `tactics`.

For a guided introduction to proofs using tactics, see

Natural Number Game:
https://adam.math.hhu.de/#/g/leanprover-community/nng4

In the game, you can switch to writing the Lean code directly by
clicking the `</>` button in the top right corner.
-/

/- Theorems are special types of function definitions. They can be
introduced using the `theorem` or `example` keywords. In contrast to
theorems, examples don't have names. -/


example (a b : Real) : a + b = b + a := by
  rw [add_comm]

example (a b : Real) : a + b = b + a := by
  apply add_comm

example (a b : Real) : a + b = b + a := by
  ring
