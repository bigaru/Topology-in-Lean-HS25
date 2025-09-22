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


-- `∃`
example : ∃ n : ℕ, n = n := by
  use 42

example (h : ∃ n : ℕ, n > 0) : True := by
  obtain ⟨x,hx⟩ := h
  trivial

end Logic
