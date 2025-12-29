import Mathlib.Tactic

variable {α : Type} (A B C : Set α)

-- # Set identities

-- ## Boolean algebra
-- Idempotence
example : A ∪ A = A := by sorry
example : A ∩ A = A := by sorry

-- Identity
example : A ∩ ∅ = ∅ := by sorry
example : A ∪ Set.univ = Set.univ := by sorry

-- Commutativity
example : A ∩ B = B ∩ A := by sorry
example : A ∪ B = B ∪ A := by sorry

-- Associativity
example : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by sorry
example : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by sorry

-- Distributivity
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by sorry
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by sorry

-- DeMorgan
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by sorry
example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by sorry

-- ## Empty set
example : A = ∅ ↔ ∀ x : α, ¬(x ∈ A) := by sorry
example : A ≠ ∅ ↔ ∃ x, x ∈ A := by sorry
example : A ∩ B = ∅ ↔ A ⊆ Bᶜ := by sorry

-- ## Containment properties
example : A ⊆ B → B ⊆ A → A = B := by sorry
example : A ⊆ B ↔ A ∪ B = B := by sorry
example : A ⊆ B ↔ A ∩ B = A := by sorry
example : A ⊆ B → B ⊆ C → A ⊆ C := by sorry
example : A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C := by sorry
example : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by sorry
example {F G : Set (Set α)} (h : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by sorry
example {F G : Set (Set α)} (h : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by sorry

-- # Functions

variable {β : Type} (U V : Set β) (f : α → β)

-- ## Images
example (hab : A ⊆ B) : f '' A ⊆ f '' B := by sorry
example : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by sorry
example : f '' (A  ∩ B) ⊆  (f '' A) ∩  (f '' B) := by sorry
example {F : Set (Set α)} : f '' ⋃₀ F = ⋃₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by sorry
example {F : Set (Set α)} : f '' ⋂₀ F ⊆ ⋂₀ {V : Set β | ∃ U ∈ F, V = f '' U} := by sorry

-- ## Preimages
example (huv : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by sorry
example : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  := by sorry
example :  f ⁻¹' (U  ∪ V ) = (f ⁻¹' U) ∪ (f ⁻¹' V ) := by sorry
example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by sorry
example {F : Set (Set β)} : f ⁻¹' (⋂₀ F ) = ⋂₀ { (f ⁻¹' V) | V ∈ F} := by sorry
example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃ (V : Set β) (hV: V ∈  F), f ⁻¹' V := by sorry
example {F : Set (Set β)} : f ⁻¹' (⋃₀ F ) = ⋃₀ {(f ⁻¹' V) | V ∈  F} := by sorry

-- ## Interaction
-- Loop
example : f '' (f ⁻¹' V ) ⊆ V := by sorry
example : A ⊆ f ⁻¹' (f '' A) := by sorry
-- Galois connection
example : f '' A ⊆ U ↔ A ⊆ f ⁻¹' U := by sorry
