import Mathlib.Tactic

/-
# Sets

Given a type `α : Type`, there is a type `Set α` whose members are sets with elements of type `α`.

`Set α` is equivalent to `α → Prop`.
You should think of `X : α → Prop` as sending `s ↦ (s ∈ X)`, where `s ∈ X` is the proposition stating that `s` is an element of `X`.
This is similar to an indicator function.

Hence, to prove `s ∈ X`, you must provide a witness `p : X s`.

There is also `s ∉ X := ¬(s ∈ X)`. (\notin)
-/

variable (α : Type) (X Y Z : Set α)
open Set

-- ## Defining sets

-- Finite sets can be defined by listing their elements:
def nums : Set ℕ := {1,2,3}

-- General sets can be defined by set builder notation
def evens := {x : ℕ | ∃ k : ℕ, x = 2*k}
def evens' : Set ℕ  := {x | ∃ k : ℕ, x = 2*k}

-- This above is syntactic sugar for the anonymous function
def evens'' : Set ℕ := fun x => ∃ k : ℕ, x = 2*k

-- To show `2 ∈ evens`, we need to prove that `∃ k : ℕ, 2 = 2*k`
example : 2 ∈ evens := by
  use 1

/- For any type `α` there is
- a universal set `univ : Set α` defined by `{x : α | True}`
- an empty set `∅ : Set α` defined by `{x : α | False}`
-/

-- ## Membership and inclusion
/-
Inclusion `X ⊆ Y` is defined by `∀ x : α, x ∈ X → x ∈ Y`.
Treat like `∀` / `→` in proofs.
-/

example (x : α) (hx : x ∈ X) (hi : X ⊆ Y) : x ∈ Y := by
  apply hi
  exact hx

example (x : α) (hx : x ∈ X) (hi : X ⊆ Y) : x ∈ Y := by
  specialize hi hx
  exact hi

example (hl : X ⊆ Y) (hr : Y ⊆ X) : X = Y := by
  ext s -- This introduces a new hypothesis `s : α` and changes the goal to `s ∈ X ↔ s ∈ Y`
  constructor
  case mp =>
    apply hl
  case mpr =>
    apply hr

-- ## Set operations
/-
Binary union `∪` (\cup)
`X ∪ Y := {x | x ∈ X ∨ x ∈ Y}`
Treat like `∨` in proofs

Binary intersection `∩` (\cap)
`X ∩ Y := {x | x ∈ X ∧ x ∈ Y}`
Treat like `∧` in proofs

Intersection binds tighter than union.

Set difference `\` (\\) NOT JUST BACKSLASH!
`X \ Y := {x | x ∈ X ∧ x ∉ Y}`
Treat like `∧`, then `¬`.

Complements `ᶜ` (\compl)
`Xᶜ := {x | x ∉ X}`
Treat like `¬`.
-/

-- ### Example 1
-- Proof by using rewrites
example : X ∩ Y ⊆ X ∪ Y := by
  rw [subset_def]
  intro x hx
  rw [inter_def, mem_setOf] at hx -- alternative `mem_inter_iff`
  rw [union_def, mem_setOf] -- alternative `mem_union`
  left
  exact hx.left

-- Proof using simp
example : X ∩ Y ⊆ X ∪ Y := by
  rw [subset_def]
  intro x hx
  simp at hx -- alternative `mem_inter_iff`
  simp -- alternative `mem_union`
  left
  exact hx.left

-- Shorter proof directly using 'definitional reduction'
example : X ∩ Y ⊆ X ∪ Y := by
  intro x hx
  left
  exact hx.left

-- ### Example 2
-- Proof using 'definitional reduction'
example (h : X ⊆ Y) : X ∩ Z ⊆ Y ∩ Z := by
  intro x hx
  constructor
  case left =>
    exact h hx.left
  case right =>
    exact hx.right

-- Even shorter
example (h : X ⊆ Y) : X ∩ Z ⊆ Y ∩ Z := by
  intro x hx
  exact ⟨h hx.left, hx.right⟩

-- ### Example 3

example : X ∩ (Y ∪ Z) ⊆ (X ∩ Y) ∪ (X ∩ Z) := by
  intro x hx
  obtain hy | hz := hx.right
  case inl =>
    left
    constructor
    case left =>
      exact hx.left
    case right =>
      exact hy
  case inr =>
    right
    constructor
    case left =>
      exact hx.left
    case right =>
      exact hz

-- Shortened
example : X ∩ (Y ∪ Z) ⊆ (X ∩ Y) ∪ (X ∩ Z) := by
  intro x hx
  obtain hy | hz := hx.right
  case inl =>
    left
    exact ⟨hx.left, hy⟩
  case inr =>
    right
    exact ⟨hx.left, hz⟩

-- ### Example 4
example (h : Y ⊆ Z) : X \ Z ⊆ X \ Y := by
  intro x hx
  have wx : x ∈ X := hx.left
  have wnz : x ∉ Z := hx.right
  constructor
  case left =>
    exact wx
  case right =>
    intro t
    have wz : x ∈ Z := h t
    contradiction

-- ### Example 5
example : ∅ᶜ = (univ : Set α) := by
  ext x
  constructor
  case mp =>
    intro hx
    trivial
  case mpr =>
    intro hx xe
    contradiction

/-
Indexed unions (iUnion):
Given a function `A : I → Set α`, there is a type
`⋃ i : I, A i` that represents the union over all sets `A i`.
WARNING: (\U or \bigcup) not the same symbol as binary union

Indexed intersection (iInter)
Given a function `A : I → Set α`, there is a type
`⋂ i : I, A i` that represents the union over all sets `A i`.
WARNING: (\I or \bigcap) not the same symbol as binary intetsection

Use simp or Mathlib definitions to rewrite these.
-/

example (I : Type) (A : I → Set α) (x : α) (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i := by
  rw [mem_iUnion] -- you can use `simp` instead
  use i

/-
Unions over a set (sUnion):
Given a set of sets `s : Set (Set α)`, there is a type
`⋃₀ s` that represents the union over all sets in `s`.
WARNING: (\U\0 or \bigcup\0) not the same symbol as binary union

Intersection over a set (sInter):
Given a set of sets `s : Set (Set α)`, there is a type
`⋂₀ s` that represents the intersection over all sets in `s`.
WARNING: (\I\0 or \bigcap\0) not the same symbol as binary intetsection

Use simp or Mathlib definitions to rewrite these.
-/

example (A B : Set α) :  ⋂₀ {A,B} = A ∩ B := by
  -- we do not use `simp` since the statement is already a tagged theorem.
  ext x
  constructor
  case mp =>
    intro hx
    rw [mem_sInter] at hx
    have ha : x ∈ A := by
      specialize hx A
      apply hx
      simp
    have hb : x ∈ B := by
      specialize hx B
      apply hx
      simp
    constructor
    case left => exact ha
    case right => exact hb
  case mpr =>
    intro hx
    rw [mem_sInter]
    intro t ht
    obtain ht1 | ht2 := ht
    case inl =>
      rw [← ht1] at hx
      exact hx.1
    case inr =>
      rw [mem_singleton_iff] at ht2
      rw [← ht2] at hx
      exact hx.2

/- # Functions
We can use the usual function type `f : α → β` to express functions.

If `Y : Set β`, then `preimage f Y := {x : α | f x ∈ Y}`.
One can write `f⁻¹' Y` (\-1) for the pre-image.

If `X : Set α`, then `image f X := {y : β | ∃ x : α, x ∈ X ∧ f x = y}`.
One can write `f '' X` for the image (with a space before '').
-/

variable (β : Type) (f : α → β) (U : Set β)

example : f '' (X ∪ Y) = (f '' X) ∪ (f '' Y) := by
  ext y
  constructor
  case mp =>
    intro hy
    simp at hy
    obtain ⟨x,xu,hfxy⟩ := hy
    obtain xx | xy := xu
    case inl =>
      left
      use x
    case inr =>
      right
      use x
  case mpr =>
    intro hy
    simp at hy
    obtain ⟨x,xu,hfxy⟩ | ⟨x,xu,hfxy⟩ := hy
    case inl =>
      have xxy : x ∈ X ∪ Y := by
        left
        exact xu
      use x
    case inr =>
      have xxy : x ∈ X ∪ Y := by
        right
        exact xu
      use x

/- # Subtypes
You may have noticed that we define functions between types, not sets.
We can move from sets to types by using the subtype construction.

Given a set `S : Set X`, the subtype `↥S` (\u-|) is the type of elements of `X` that are in `S`.
An element of `↥S` is a pair `⟨x, hx⟩` consisting of
- an element `x : X`
- a proof `hx : x ∈ S`

If `y : ↥S`, its components can be accessed as
`y.val` / `y.1` (the element)
`y.property` / `y.2` (the proof).

There is a canonical inclusion map from `↥S` to `X`.
For `x : ↥S`, the corresponding element of `X` is written as `↑x` (\u-).

Just as sets can be defined by `{x : X | P x}`,
subtypes can be constructed using `{x : X // P x}`
-/
