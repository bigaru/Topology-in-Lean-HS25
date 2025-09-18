import Mathlib.Tactic

-- # Exercise 1: Logic
variable (p q r s : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by sorry
example : p ∨ q ↔ q ∨ p := by sorry

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by sorry

-- Distributivity of ∧ with respect to ∨ and vice versa
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by sorry

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := by sorry
example : ¬(p ∧ ¬p) := by sorry
example : p ∧ ¬q → ¬(p → q) := by sorry
example : ¬p → (p → q) := by sorry
example : (¬p ∨ q) → (p → q) := by sorry
example : p ∨ false ↔ p := by sorry
example : p ∧ false ↔ false := by sorry

-- Classical reasoning required (`by_contra`, `by_cases`, `push_neg`)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := by sorry
example : ¬(p → q) → p ∧ ¬q := by sorry
example : (p → q) → (¬p ∨ q) := by sorry
example : (¬q → ¬p) → (p → q) := by sorry
example : p ∨ ¬p := by sorry
example : (((p → q) → p) → p) := by sorry
