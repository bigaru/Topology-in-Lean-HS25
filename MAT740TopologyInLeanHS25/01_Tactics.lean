import Mathlib.Tactic

/-
Tactics documentation:
https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/#tactics

Tactics cheat sheet:
https://leanprover-community.github.io/papers/lean-tactics.pdf
-/


-- # Basic tactics that manipulate the context and apply lemmas.
section Context

variable (p q r : Prop)
/- Introduce `p, q, r` as fixed arbitrary propositions.
They will be part of the context of every proof in the section,
so we can reference them without having to introduce them each time -/

-- `rfl` proves goals of the form `p = p` and `p ↔ p`
example : p = p := by
  rfl

example : p ↔ p := by
  rfl

-- `exact` proves a goal if it is exactly the same as one of the hypotheses
example (h : p) : p := by
  exact h

-- `apply` rewrites a hypothesis or the goal using an implication
example (h : p → q) (hp : p) : q := by
  apply h at hp -- apply h to hp
  exact hp -- use hp to prove the goal

example (h : p → q) (hp : p) : q := by
  apply h -- apply h to the goal
  exact hp -- use hp to prove the goal

-- You can also directly apply hypotheses by function application
example (h : p → q) (hp : p) : q := by
  exact h hp -- `h hp` is `h` applied to `hp` and hence has type `q`


-- `rw [h]` allows you to rewrite (parts) of the goal or hypothesis
-- use `rw [← h]` to rewrite using opposite direction
example (h : p = q) : q = p := by
  rw [h] -- rewrite goals using `rw`

example (hpq : p = q) (hqr : q = r) : p = r := by
  rw [← hpq] at hqr -- rewrite goals using `rw [_] at _`
  exact hqr

-- Use `nth_rw k` for rewriting the k-th occurrence

-- `have` introduces a new hypothesis, which we must prove first
example (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  have hq : q := by
    apply hpq at hp
    exact hp
  apply hqr at hq
  exact hq

-- `ext` reduces an equality type to its definition
example (h : p ↔ q) : p = q := by
  ext
  exact h

end Context

-- # Dealing with logic
section Logic

variable (p q r : Prop)

-- ## Universal quantifier `∀` (\forall, \for)
example : ∀ n : ℕ, n = n := by
  intro n -- use `intro` if `∀` appears in goal
  rfl

example (h : ∀ n : ℕ, n = 1) : 0 = 1 := by
  apply h -- use `apply` if `∀` appears in hypothesis

example (h : ∀ n : ℕ, n = 1) : 0 = 1 := by
  specialize h 0 -- use `specialize h x` apply universal statement `h` to instance `x`
  exact h

-- ## Implication `→` (\to)
example : p → p := by
  intro h -- use `intro` if `→` appears in goal
  exact h

example (h : p → q) (hp : p) : q := by
  apply h -- use `apply` if `→` appears in hypothesis
  exact hp

-- ## Negation `¬` (\neg).
-- ¬p equals p → False by definition

example : ¬ (False) := by
  intro h -- use `intro` if `¬` appears in goal
  exact h

example (h : ¬p) : p → q := by
  intro hp
  apply h at hp -- use `apply` if `¬` appears in hypothesis
  contradiction -- If `False` appears as hypothesis, use `contradiction`

example (h1 : p) (h2 : ¬p) : False := by
  contradiction -- use `contradiction` when there are two opposing hypotheses.

-- ## Conjunction `∧` (\and)
example (hp : p) : p ∧ p := by
  constructor -- use `constructor` if `∧` appears in goal to get two sub-goals
  case left =>
    exact hp
  case right =>
    exact hp

-- You may use the dot · (\.) notation for a more compact proof
example (hp : p) : p ∧ p := by
  constructor
  · exact hp
  · exact hp

-- Finally, you can directly construct the witness using ⟨.,.⟩ (\< \>)
example (hp : p) : p ∧ p := by
  exact ⟨hp,hp⟩

example (hpq : p ∧ q) : p := by
  obtain ⟨hp, hq⟩ := hpq -- use `obtain` to unpack `∧` in hypothesis. Angle brackets (\<, \>)
  exact hp

/-You can also directly access the components of
  the conjunction using `.left` and `.right`, or `.1` and `.2` -/
example (hpq : p ∧ q) : p := by
  exact hpq.left

-- ## Bi-implication `↔` (\iff)
example : p ↔ p := by
  constructor -- use `constructor` is `↔` appears in goal
  case mp => -- modus ponens
    intro hp
    exact hp
  case mpr => -- modus ponens reverse
    intro hp
    exact hp

example (hpq : p ↔ q) (hq : q) : p := by
  rw [hpq] -- use `rw` to rewrite using bi-implication in hypothesis
  exact hq

example (hpq : p ↔ q) (hp : p) : q := by
  rw [← hpq] -- use `rw` to rewrite using bi-implication in hypothesis
  exact hp

/-You can also directly access the components of
  the conjunction using `.mp` and `.mpr`, or `.1` and `.2` -/
example (hpq : p ↔ q) (hq : q) : p := by
  apply hpq.mpr
  exact hq

-- ## Disjunction `∨` (\or)
example (hp : p) : p ∨ q := by
  left -- use `left` or `right` if `∨` appears in goal
  exact hp

example (hpq : p ∨ q) : q ∨ p := by
  obtain hp | hq := hpq -- use `obtain` to split `∨` in hypothesis into cases
  case inl =>
    right
    exact hp
  case inr =>
    left
    exact hq

-- ## Existential quantifier `∃` (\exist, \ex)
example : ∃ n : ℕ, n = n := by
  use 42 -- use `use` to provide a witness to existential statement in goal

example (h : ∃ n : ℕ, n > 0) : True := by
  obtain ⟨x, hx⟩ := h -- use `obtain` to get witness and property from existential hypothesis
  trivial -- use `trivial` to prove `True`

end Logic

-- # Reasoning techniques
section Reasoning

variable (p : Prop)

-- ## Proof by contradiction
example : (¬ ¬ p) → p := by
  intro h
  by_contra g -- `by_contra` adds negation of goal as new hypothesis
  exact h g

-- ## Pushing negations
example : ¬ (∀ n : ℕ, n = 0) := by
  push_neg -- Push negation through quantifier at goal
  use 1
  exact one_ne_zero

example (h : ¬ (∃ n : ℕ, n = 0)) : False := by
  push_neg at h -- Push negations at hypothesis
  have z : 0 = 0 := by rfl
  apply h at z
  exact z

-- ## Proof by cases
example : p ∨ ¬p := by
  by_cases h : p -- split into two goals with extra hypotheses `p` and `¬ p`, respectively
  case pos =>
    left
    exact h
  case neg =>
    right
    exact h

-- ## Induction
example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      apply Nat.le_add_right_of_le
      exact ih

end Reasoning

/- # Searching

Get suggestions with
`exact?`,
`apply?`,
`rw?`,
`have? using h1, h2`,
`hint`

Search Mathlib docs:
https://leanprover-community.github.io/mathlib4_docs/index.html

Search Loogle with
#loogle

Ask copilot for help.
-/


-- # Automation

-- `repeat` will repeat any block of tactics until it no longer applies

-- `simp` and its variations will try to simplify using lemmas tagged with `@[simp]`

-- `tauto` for logical tautologies
example (p q : Prop) : p → (q → (p ∧ p)) := by
  tauto

-- `linarith` for linear inequalies
example (n : ℕ) : 0 ≤ n + 1 := by
  linarith

-- `ring` for commutative rings
example (l m n : ℕ) : (n + m) * l = l * m + l * n := by
  ring

-- `noncomm_ring` for general rings
-- `abel` for additive Abelian groups
-- `group` for general groups
