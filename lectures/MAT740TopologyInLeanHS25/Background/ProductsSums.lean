import Mathlib.Tactic

universe u v
variable (I : Type u) (X : I → Type v)

/- # Dependent Products -/
section Products

/- Given an indexed collection of types `X : I → Type*`, form the *dependent product* `(i : I) → X i`. -/
#check  (i : I) → X i

/-
A term `t : (i : I) → X i` is an assignment `(i : I) ↦ (t i : X i)`.

We can think of such a term as
- a dependent function that sends `i` to some `x : X i`,
- a function `t : I → Σ i, X i` such that `t i : X i`,
- a section `t : I → Σ i, X i` of the map `Σ i, X i → I` given by `⟨j,xj⟩ ↦ j`.
- an element of the product `Π i, X i` over the collection `X i`,

-/

/- Product notation is defined in Mathlib (e.g. Mathlib.Tactic) -/
#check Π i : I, X i -- (\P) or (\Pi)
#check Π i, X i

/- The universal quantifier is a special case when the collection of tyes are propositions.

Giving a term of `t : ∀ i, X i` requires providing a term `t i : X i` for every `(i : I)`.
-/
#check ∀ i, X i

/- ## Binary products as structures
Binary products `X₁ × X₂` can be thought of as a dependent product over the collection `X : 2 → Type*`.

Lean defines `Prod X₁ X₂` (as a structure) for binary products which you can write `X₁ × X₂`.

See https://leanprover.github.io/theorem_proving_in_lean4/Structures-and-Records/#structures-and-records
for more on structures.
-/

structure Prod' (α : Type u) (β : Type v) where
  /--
  Constructs a pair. This is usually written `(x, y)` instead of `Prod.mk x y`.
  -/
  mk ::
  /-- The first element of a pair. -/
  fst : α
  /-- The second element of a pair. -/
  snd : β

-- The above could also be implemented as follows:
inductive Prod'' (α : Type u) (β : Type v)
  | mk : α → β → Prod'' α β

/- You can construct terms `t : X₁ × X₂` using `Prod.mk x1 x2` or equivalently `⟨x1, x2⟩`.

The projections are named `fst` and `snd`.
E.g `x = ⟨x.fst, x.snd⟩ = ⟨x.1, x.2⟩`
-/


/- ## Universal property of products -/

theorem univ_Prod {T : Type*} (fs : Π i, (T → X i))
    : ∃! (f : T → Π i, X i), ∀ t i, f t i = fs i t := by
        /- Proof is basically trivial. -/
        let f := fun t i ↦ fs i t
        use f
        constructor
        case left => intro t i; trivial
        case right =>
            intro f' hf'; exact funext₂ hf'

end Products

/- # Dependent Sums -/
section Sums

/- Given an indexed collection of types `X : I → Type*`, form the *dependent sum* `Σ i : I, X i`. -/
#check Σ i : I, X i
#check Σ i, X i
#check (i : I) × X i

/- A term `t : Σ i, X i` has the form `⟨j, xj⟩`, where `j : I` and `xj : X j`.

We can think of `Σ i, X i` as
- the disjoint union `⨿ i, X i`
- a binary dependent product `I × (X i)` where the second component depends on the first.

Terms of `Σ i, X i` can be constructed using `Sigma.mk`.
-/

variable (j : I) (xj : X j)
#check Sigma.mk
#check Sigma.mk j xj

/- The existential quantifier `∃` is a special case where the collection of types are propositions.

Providing a term `t : Σ i, P i` requires providing a single tuple `⟨i ,h i⟩`, where `i : I` and `h i : P i` is a proof that `P` holds for `i`.
-/
variable (P : I → Prop)
#check ∃ i, P i

/- ## Binary sums as inductive types
Binary sums `X₁ ⊕ X₂` (\oplus) can be thought of as a dependent sum over the collection `X : 2 → Type*`.

Lean defines `Sum X₁ X₂` (as an inductive type) for binary sums which you can write `X₁ ⊕ X₂`.

See https://leanprover.github.io/theorem_proving_in_lean4/Inductive-Types/#inductive-types
for more on inductive types.-/

inductive Sum' (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. -/
  | inl (val : α) : Sum' α β
  /-- Right injection into the sum type `α ⊕ β`. -/
  | inr (val : β) : Sum' α β

/- You can construct terms `t : X₁ ⊕ X₂` using either `Sum.inl x₁` or `Sum.inr x₂` for `x₁ : X₁` and `x₂ : X₂`

You can define functions out of `X₁ ⊕ X₂` using pattern matching / case distinction.
-/

-- Example:
def f : ℕ ⊕ ℤ → ℤ := fun x ↦ match x with
    | Sum.inl x => x  -- do something
    | Sum.inr x => x + 1 -- do something else

/- ## Universal property of sums -/

theorem univ_Sum {T : Type*} (fs : Π i, (X i → T))
    : ∃! (f : (Σ i, X i) → T), ∀ i (x : X i), f ⟨i, x⟩ = fs i x := by
        /- Proof is basically trivial. -/
        let f := fun y ↦ match y with
            | Sigma.mk i x => fs i x
        use f
        constructor
        case left => intro i x; trivial
        case right =>
            intro f' hf'
            rw [@funext_iff]
            exact fun x ↦ hf' x.fst x.snd

end Sums
