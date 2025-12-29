import Mathlib.Tactic

-- # Exercise 1: Logic
variable (p q r s : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  case mp =>
    intro h
    exact ⟨h.right, h.left⟩
  case mpr =>
    intro h
    exact ⟨h.right, h.left⟩


example : p ∨ q ↔ q ∨ p := by
  -- By symmetry, it suffices to prove one direction for all Props
  have h : ∀ a b : Prop, a ∨ b → b ∨ a := by
    intro a b hab
    obtain ha | hb := hab
    case inl =>
      right ; exact ha
    case inr =>
      left ; exact hb
  constructor
  repeat apply h

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  case mp =>
    intro hpqr
    have ⟨⟨hp,hq⟩,hr⟩ := hpqr
    exact ⟨hp,hq,hr⟩
  case mpr =>
    intro hpqr
    have ⟨hp,hq,hr⟩ := hpqr
    exact ⟨⟨hp,hq⟩,hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  case mp =>
    intro hpqr
    obtain (hp | hq) | hr := hpqr
    case inl =>
      left ; exact hp
    case inl.inr =>
      right ; left ; exact hq
    case inr =>
      right ; right ; exact hr
  case mpr =>
    intro hpqr
    obtain hp | hq | hr := hpqr
    case inl =>
      left ; left ; exact hp
    case inr.inl =>
      left ; right ; exact hq
    case inr.inr =>
      right ; exact hr

-- Distributivity of ∧ with respect to ∨ and vice versa
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  case mp =>
    intro hpqr
    obtain ⟨hp, hq | hr⟩ := hpqr
    case inl =>
      left
      exact ⟨hp, hq⟩
    case inr =>
      right
      exact ⟨hp, hr⟩
  case mpr =>
    intro hpqpr
    obtain ⟨hp, hq⟩ | ⟨hp, hr⟩ := hpqpr
    case inl =>
      constructor
      case left =>
        exact hp
      case right =>
        left ; exact hq
    case inr =>
      constructor
      case left =>
        exact hp
      case right =>
        right ; exact hr

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  case mp =>
    intro hpqr
    obtain hp | ⟨hq, hr⟩ := hpqr
    case inl =>
      exact ⟨Or.inl hp, Or.inl hp⟩ -- `Or.inl` and `Or.inr` construct disjunctions
    case inr =>
      exact ⟨Or.inr hq, Or.inr hr⟩
  case mpr =>
    intro hpqpr
    obtain ⟨hp1 | hq, hp2 | hr⟩ := hpqpr
    case inl.inl =>
      left ; exact hp1
    case inl.inr =>
      left ; exact hp1
    case inr.inl =>
      left ; exact hp2
    case inr.inr =>
      right ; exact ⟨hq, hr⟩

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  case mp =>
    intro h1 h2
    obtain ⟨h2p, h2q⟩ := h2
    exact h1 h2p h2q
  case mpr =>
    intro h1 h2 h3
    apply h1
    exact ⟨h2, h3⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hp ; apply h ; left ; exact hp
    case right =>
      intro hq ; apply h ; right ; exact hq
  case mpr =>
    intro h hpq
    obtain hp | hq := hpq
    case inl =>
      exact h.left hp
    case inr =>
      exact h.right hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hp
      have hpq : p ∨ q := by
        left ; exact hp
      contradiction
    case right =>
      intro hq
      have hpq : p ∨ q := by
        right ; exact hq
      contradiction
  case mpr =>
    intro h
    obtain ⟨hnp, hnq⟩ := h
    intro hpq
    obtain hp | hq := hpq
    case inl => contradiction
    case inr => contradiction

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h g
  obtain ⟨hp, hq⟩  := g
  obtain hnp | hnq := h
  case inl => contradiction
  case inr => contradiction

example : ¬(p ∧ ¬p) := by
  intro h
  obtain ⟨hp,hnp⟩ := h
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
  case inl => contradiction
  case inr => exact hq

example : p ∨ False ↔ p := by
  constructor
  case mp =>
    intro h
    obtain h1 | h2 := h
    case inl => exact h1
    case inr => contradiction
  case mpr =>
    intro hp; left; exact hp

example : p ∧ False ↔ False := by
  constructor
  case mp =>
    intro h; exact h.right
  case mpr =>
    intro f; contradiction

-- Classical reasoning required (`by_contra`, `by_cases`, `push_neg`)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro h
  by_cases c : p
  case pos =>
    specialize h c
    obtain hr | hs := h
    case inl =>
      left ; intro c' ; exact hr
    case inr =>
      right ; intro c' ; exact hs
  case neg =>
    left ; intro h ; contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases c : p
  case pos =>
    push_neg at h
    specialize h c
    right
    exact h
  case neg =>
    left ; exact c


example : ¬(p → q) → p ∧ ¬q := by
  intro h
  push_neg at h
  exact h

example : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases c : p
  case pos => right ; exact h c
  case neg => left ; exact c

example : (¬q → ¬p) → (p → q) := by
  intro h
  contrapose
  exact h

example : p ∨ ¬p := by
  by_cases c : p
  case pos => left ; exact c
  case neg => right ; exact c

example : (((p → q) → p) → p) := by
  intro h
  by_cases c : p → q
  case pos => exact h c
  case neg =>
    push_neg at c
    exact c.left
