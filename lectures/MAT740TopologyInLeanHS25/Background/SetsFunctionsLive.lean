import Mathlib.Tactic

/- # Sets

Given a type `α : Type`, there is a type `Set α` whose members are sets with elements of type `α`.

`Set α` is equivalent to `α → Prop`.
You should think of `X : α → Prop` as sending `s ↦ (s ∈ X)`, where `s ∈ X` is the proposition that `s` is an element of `X`.
This is similar to an indicator function.

Hence, for `s : α` to prove `s ∈ X` (\in), then you must provide a proof / witness that `p : X s`.

There is also `s ∉ X := ¬(s ∈ X)`. (\notin)
-/

variable (α : Type) (X Y Z : Set α)

-- # Defining Sets

def nums : Set ℕ := {1,2,3}

def evens := {x : ℕ | ∃ k : ℕ, x = 2*k}
def evens' : Set ℕ := {x | ∃ k : ℕ, x = 2*k}

-- Both of the above are syntactic sugar for the following anonymous function
def evens'' : Set ℕ := fun x => ∃ k : ℕ, x = 2*k

-- To show that `2 ∈ evens`, we need to prove `∃ k : ℕ, 2 = 2*k`
example : 2 ∈ evens := by
  use 1

/- For any type `α` there is
- a universal set `Set.univ : Set α` defined by {x : α | True}
- an empty set `∅ : Set α` (\empty) defined by {x : α | False}
-/

-- ## Membership and inclusion
/-
Inclusion `X ⊆ Y` (\sub) is defined by `∀ x : α, x ∈ X → x ∈ Y`.
Treat like `∀ / →` in proofs (intro / apply / specialize)
-/

example (x : α) (hx : x ∈ X) (hi : X ⊆ Y) : x ∈ Y := by
  apply hi
  exact hx

example (x : α) (hx : x ∈ X) (hi : X ⊆ Y) : x ∈ Y := by
  rw [Set.subset_def] at hi
  apply hi
  exact hx

example (x : α) (hx : x ∈ X) (hi : X ⊆ Y) : x ∈ Y := by
  specialize hi hx
  exact hi

/-
Equality of sets
-/

example (hl : X ⊆ Y) (hr : Y ⊆ X) : X = Y := by
  ext x -- use `ext` if equality of sets in goal
  constructor
  case mp => apply hl
  case mpr => apply hr

-- ## Set operations
/-
Binary union `∪` (\cup)
`X ∪ Y := {x | x ∈ X ∨ x ∈ Y}`
Treat like `∨` in proofs

Binary intersection `∩` (\cap)
`X ∩ Y := {x | x ∈ X ∧ x ∈ Y}`
Treat like `∧` in proofs

Intersection bind tighter than unions.

Set difference `\` (\\) NOT JUST BACKSLASH!
`X \ Y := {x | x ∈ X ∧ x ∉ Y}`
Treat like a combination of `∧` and `¬` in proofs.

Complements `ᶜ` (\compl)
`Xᶜ := {x : α | x ∉ X}`
Treat like `¬` in proofs
-/

open Set

-- ### Example 1

example : X ∩ Y ⊆ X ∪ Y := by
  rw [subset_def]
  intro x hx
  rw [inter_def, mem_setOf] at hx
  rw [union_def, mem_setOf]
  left
  exact hx.left

example : X ∩ Y ⊆ X ∪ Y := by
  intro x hx
  left
  exact hx.left

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
    have wz : x ∈ Z := by
      exact h t
    contradiction

-- ## Indexed unions and intersections
/-
Unions over a set (iUnion):
Given a function `A : I → Set α`, there is a type
`⋃ i : I, A i`  / `⋃ i, A i` (\bigcup) that represents the union over all sets `A i`
WARNING: NOT (\cup)

Intersections over a set (iInter):
Given a function `A : I → Set α`, there is a type
`⋂ i : I, A i`  / `⋂ i, A i` (\bigcap) that represents the intersection over all sets `A i`
WARNING: NOT (\cup)
-/

/-
Unions over a set (sUnion):
Given a set of sets `s : Set (Set α)`, there is a type
`⋃₀ s` (\bigcup \0) that represents the unions over all sets in `s`.
WARNING: NOT (\cup)

Intersections over a set (sInter):
Given a set of sets `s : Set (Set α)`, there is a type
`⋂₀ s` (\bigcap \0) that represents the intersection over all sets in `s`.
WARNING: NOT (\cup)
-/

example (A : Set α) : ⋂₀ {A} = A := by
  ext x; constructor
  case mp =>
    intro hx
    rw [mem_sInter] at hx
    specialize hx A
    apply hx
    trivial
  case mpr =>
    intro hx
    rw [mem_sInter]
    intro t ht
    rw [mem_singleton_iff] at ht
    rw [ht]
    exact hx

/- # Functions
We can use the function type `f : α → β` to functions.

If `Y : Set β`, there is a set `preimage f Y := {x : α  | f x ∈ Y}`.
One can write `f ⁻¹' Y` (\-1)

If `X : Set α`, there is a set `image f X := {y : β | ∃ x : α, x ∈ X ∧ f x = y}`.
One can write `f '' X` for the image
Treat like `∃` in proofs.
-/

variable (β : Type) (f : α → β)

example : f '' (X ∪ Y) = (f '' X) ∪ (f '' Y) := by
  ext u; constructor
  case mp =>
    intro hx
    rw [mem_image] at hx
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := hx
    obtain hxx | hxy := hx1
    case inl =>
      left
      use x
    case inr =>
      right
      use x
  case mpr => sorry
