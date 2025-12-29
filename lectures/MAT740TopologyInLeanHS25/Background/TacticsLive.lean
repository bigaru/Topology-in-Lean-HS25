import Mathlib.Tactic

section Context

variable (p q r : Prop)

-- `rfl`
example : p = p := by
  rfl

example : p ↔ p := by
  rfl

-- `exact`
example (h : p) : p := by
  exact h

-- `apply`
example (h : p) : p := by
  apply h

example (h : p → q) (hp : p) : q := by
  apply h at hp
  exact hp

example (h : p → q) (hp : p) : q := by
  apply h
  exact hp

example (h : p → q) (hp : p) : q := by
  exact (h hp)

-- `rw [h]` allows to rewrite expression
example (h : p = q) : q = p := by
  rw [h]

-- `nth_rewrite k [h]` rewrites k-th occurrence

-- `have` introduces new hypothesis
example (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  have hq : q := by
    apply hpq
    exact hp
  apply hqr at hq
  exact hq

-- `ext` reduces an equality to its definition
example (h : p ↔ q) : p = q := by
  ext
  exact h

end Context

section Logic

variable (p q r : Prop)

-- `∀`
example : ∀ n : ℕ, n = n := by
  intro x
  rfl

example (h : ∀ n : ℕ, n = 1) : 0 = 1 := by
  apply h

example (h : ∀ n : ℕ, n = 1) : 0 = 1 := by
  specialize h 0
  exact h

-- `→`
example : p → p := by
  intro x
  exact x

-- use apply if `→` occurs in hypothesis.

-- `¬`
-- `¬p`is equivalent to `p → False` (¬ acts like implication)
example : ¬ (False) := by
  intro x
  exact x

example (h1 : p) (h2 : ¬p) : False := by
  contradiction

example (h1 : p) (h2 : ¬p) : False := by
  apply h2 at h1
  exact h1

-- `∧`
example (hp : p) : p ∧ p := by
  constructor
  case left =>
    exact hp
  case right =>
    exact hp

example (hp : p) : p ∧ p := by
  exact ⟨hp,hp⟩

example (hpq : p ∧ q) : p := by
  obtain ⟨h1,h2⟩ := hpq
  exact h1

example (hpq : p ∧ q) : p := by
  exact hpq.left

-- `↔`
-- works like `∧`
example : p ↔ q := by
  constructor
  case mp =>
    sorry
  case mpr =>
    sorry

example (hpq : p ↔ q) (hq : q) : p := by
  apply hpq.mpr
  exact hq

-- `∨`
example (hp : p) : p ∨ q := by
  left
  exact hp

example (hp : p) : p ∨ q := by
  exact Or.inl hp -- `Or.inl` and `Or.inr` can construct disjunctions

example (hpq : p ∨ q) : q ∨ p := by
  obtain hp | hq := hpq
  case inl =>
    right
    exact hp
  case inr =>
    left
    exact hq

-- `∃`
example : ∃ n : ℕ, n = n := by
  use 42

example (h : ∃ n : ℕ, n > 0) : True := by
  obtain ⟨x,hx⟩ := h
  trivial

end Logic

-- # Reasoning techniques

section Reasoning

variable (p : Prop)

-- Proof by contradiction
example : (¬ ¬ p) → p := by
  intro h
  by_contra g
  contradiction

-- Push negations through quantifiers
example : ¬ (∀ n : ℕ, n = 0) := by
  push_neg
  use 1
  exact one_ne_zero

example (h : ¬ (∃ n : ℕ, n = 0)) : False := by
  push_neg at h
  have z : 0 = 0 := by rfl
  apply h at z
  contradiction

-- Proof by cases
example : p ∨ ¬p := by
  by_cases h : p
  case pos =>
    left ; exact h
  case neg =>
    right ; exact h

-- Induction
example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    exact Nat.le_add_right_of_le ih

end Reasoning


/- # Searching

Get suggestions with
`exact?`
`apply?`
`rw?`
`have?`
`hint`

Ask AI.

Search Mathlib docs:

Search Loogle
-/

-- # Automation

-- `repeat` will repeat any block of code until it no longer applies

-- `simp` and its variations will try to simplify the goal
-- `simp at h` will simplify the hypothesis
-- @[simp]

-- `tauto` for logical tautologies
example (p q : Prop) : p → (q → (p ∧ p)) := by
  tauto

-- `linarith` for linear inequalities
example (n : ℕ) : 0 ≤ n + 1 := by
  linarith

-- `ring` for commutative rings
example (l m n : ℕ) : (n + m) * l = l * m + l * n := by
  ring

-- `noncomm_ring`
-- `abel`
-- `group`
