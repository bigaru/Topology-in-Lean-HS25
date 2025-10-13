import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions


variable {α : Type} (A B C : Set α)
variable {β : Type} (U V : Set β) (f : α → β)

example (hab : A ⊆ B) : f '' A ⊆ f '' B := by
  intro y hy
  obtain ⟨x, hx⟩ := hy -- treat hy like ∃
  obtain ⟨hA, hfx⟩ := hx
  rw [← hfx]
  exact ⟨x, hab hA, rfl⟩


example (huv : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  intro y hy
  apply huv at hy
  exact hy

example : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  := by
  ext x
  constructor
  · intro h
    rw [← Set.preimage_inter]
    exact h

  · intro h
    rw [← Set.preimage_inter] at h
    exact h


example : f '' (f ⁻¹' V ) ⊆ V := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨h1, h2⟩ := hy
  rw [Set.mem_preimage] at h1
  rw [← h2]
  exact h1

example : A ⊆ f ⁻¹' (f '' A) := by
  intro x hx
  rw [Set.mem_preimage]
  rw [Set.mem_image]
  use x

example : f '' A ⊆ U ↔ A ⊆ f ⁻¹' U := by
  constructor
  · intro h
    rw [Set.image_subset_iff] at h
    exact h
  · intro h
    rw [Set.image_subset_iff]
    exact h


universe u v
variable {X : Type u} {Y : Type v} [Topology X] [Topology Y]

theorem Cont_preimage_Closed_iff (f : X → Y) : Cont f ↔ (∀ s, Closed s → Closed (f ⁻¹' s)) := by
  constructor
  · intro h
    intro s hs
    rw [Closed]
    rw [Closed] at hs

    rw [← Set.preimage_compl]
    apply h at hs
    exact hs

  · intro h
    intro s hs

    specialize h s
    repeat rw [Closed] at h
    rw [← Set.preimage_compl] at h
    sorry
