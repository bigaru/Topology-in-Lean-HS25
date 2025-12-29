import Mathlib.Tactic

-- # Exercise 1: Logic
variable (p q r s : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  case mp =>
    intro h
    constructor
    case left => exact h.2
    case right => exact h.1

  case mpr =>
    intro h
    constructor
    case left => exact h.2
    case right => exact h.1

example : p ∨ q ↔ q ∨ p := by
  constructor
  case mp =>
    intro h
    obtain hp|hq := h

    case inl =>
      right
      exact hp
    case inr =>
      left
      exact hq

  case mpr =>
    intro h
    obtain hq|hp := h

    case inl =>
      right
      exact hq
    case inr =>
      left
      exact hp

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro h
    obtain ⟨hpq, hr⟩ := h

    constructor
    · exact hpq.1
    · constructor
      · exact hpq.2
      · exact hr

  · intro h
    obtain ⟨hp, hqr⟩  := h

    constructor
    · constructor
      · exact hp
      · exact hqr.1
    · exact hqr.2

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    rw [or_assoc] at h

    obtain hp|hqr := h
    · left
      exact hp
    · right
      obtain hq|hr := hqr
      · left
        exact hq
      · right
        exact hr

  · intro h
    rw [or_assoc]

    obtain hp|hqr := h
    · left
      exact hp
    · right
      obtain hq|hr := hqr
      · left
        exact hq
      · right
        exact hr

-- Distributivity of ∧ with respect to ∨ and vice versa
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    obtain ⟨hp, hqr⟩ := h
    obtain hq|hr := hqr
    · left
      constructor
      · exact hp
      · exact hq
    · right
      constructor
      · exact hp
      · exact hr

  · intro h
    obtain hpq|hpr := h

    case inl =>
      constructor
      case left =>
        obtain ⟨hp, hq⟩ := hpq
        exact hp
      case right =>
        obtain ⟨hp, hq⟩ := hpq
        left
        exact hq

    case inr =>
      constructor
      case left =>
        obtain ⟨hp, hr⟩ := hpr
        exact hp
      case right =>
        obtain ⟨hp, hr⟩ := hpr
        right
        exact hr


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    constructor
    · obtain hp|hqr := h
      · left
        exact hp
      · right
        obtain ⟨hq, hr⟩ := hqr
        exact hq

    · obtain hp|hqr := h
      · left
        exact hp
      · right
        obtain ⟨hq, hr⟩ := hqr
        exact hr

  · intro h
    obtain ⟨hp1 | hq, hp2 | hr⟩ := h
    · left
      exact hp1
    · left
      exact hp1
    · left
      exact hp2
    · right
      exact ⟨hq, hr⟩


-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · intro h1 h2
    obtain ⟨h2p, h2q⟩ := h2
    exact h1 h2p h2q
  · intro h1 h2 h3
    apply h1
    exact ⟨h2, h3⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  · intro h hpq
    obtain hp | hq := hpq
    · exact h.left hp
    · exact h.right hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro h
    constructor
    · intro hp
      have hpq : p ∨ q := by
        left
        exact hp
      contradiction
    · intro hq
      have hpq : p ∨ q := by
        right
        exact hq
      contradiction
  · intro h
    obtain ⟨hnp, hnq⟩ := h
    intro hpq
    obtain hp | hq := hpq
    · contradiction
    · contradiction

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h g
  obtain ⟨hp, hq⟩  := g
  obtain hnp | hnq := h
  · contradiction
  · contradiction

example : ¬(p ∧ ¬p) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro h g
  have hq : q := by
    exact g h.left
  have hnq : ¬q := by
    exact h.right
  contradiction

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  obtain hnp | hq := h
  · contradiction
  · exact hq

example : p ∨ False ↔ p := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · exact h1
    · contradiction
  · intro hp
    left
    exact hp

example : p ∧ False ↔ False := by
  constructor
  · intro h
    exact h.right
  · intro f
    contradiction

-- Classical reasoning required (`by_contra`, `by_cases`, `push_neg`)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := by sorry
example : ¬(p → q) → p ∧ ¬q := by sorry
example : (p → q) → (¬p ∨ q) := by sorry
example : (¬q → ¬p) → (p → q) := by sorry
example : p ∨ ¬p := by sorry
example : (((p → q) → p) → p) := by sorry
