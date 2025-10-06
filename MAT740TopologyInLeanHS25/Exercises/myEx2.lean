import Mathlib.Tactic


-- # Exercise 1: Logic
variable (p q r s : Prop)

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_contra g
  push_neg at g
  exact h g

example : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases hc: p
  · apply h at hc
    right
    exact hc
  · left
    exact hc

example : (((p → q) → p) → p) := by
  intro h
  by_cases hp: p
  · apply hp
  · apply h
    intro h2
    contradiction

variable {α : Type} (A B C : Set α)

-- ## Boolean algebra
-- Idempotence
example : A ∪ A = A := by
  ext x
  constructor
  · intro h
    obtain A1 | A2 := h
    · exact A1
    · exact A2
  · intro h
    left
    exact h

-- Identity
example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · intro h
    obtain ⟨hA, hE⟩  := h
    exact hE
  · intro h
    constructor
    · contradiction
    · exact h


-- DeMorgan
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro h
    rw [Set.mem_compl_iff, Set.mem_union] at h
    push_neg at h
    obtain ⟨A, B⟩ := h
    constructor
    · exact A
    · exact B
  · intro h
    rw [Set.mem_compl_iff, Set.mem_union]
    push_neg
    obtain ⟨A, B⟩ := h
    constructor
    · exact A
    · exact B

-- ## Containment properties
example : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h
    ext x
    constructor
    · intro h2
      obtain ⟨A, B⟩ := h2
      exact A
    · intro h2
      constructor
      · exact h2
      · apply h at h2
        exact h2

  · intro h
    intro x hx
    rw [← h] at hx
    obtain ⟨A, B⟩ := hx
    exact B
