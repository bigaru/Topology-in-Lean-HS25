import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u
open Set

class Basis (X : Type u) : Type u where
  Basics : Set (Set X)
  Basis_cover : ⋃₀Basics = univ
  Basis_inter : ∀ b1 ∈ Basics, ∀ b2 ∈ Basics, ∀ x ∈ b1 ∩ b2, ∃ b3 ∈ Basics, x ∈ b3 ∧ b3 ⊆ b1 ∩ b2

-- `∀ x ∈ A, phi x` is equivalent to `∀ x : X, x ∈ A → phi x`
-- `∃ x ∈ A, phi x` is equivalent to `∃ x : X, x ∈ A ∧ phi x`

variable {X : Type u} [B : Basis X]

@[simp]
theorem Basis_cover : ⋃₀B.Basics = univ := B.Basis_cover

theorem Basis_cover_x (x : X) : ∃ bx ∈ B.Basics, x ∈ bx := by
  rw [← mem_sUnion, Basis_cover]
  trivial

instance basisTopology : Topology X where
  Open := fun U ↦ ∀ x ∈ U, ∃ bx ∈ B.Basics, x ∈ bx ∧ bx ⊆ U
  Open_univ := by
    intro x hx
    simp only [subset_univ, and_true]
    apply Basis_cover_x
  Open_inter := by
    intro U V open_U open_V x hx
    specialize open_U x hx.left
    obtain ⟨bUx, hbUx1, hbUx2, hbUx3⟩ := open_U
    specialize open_V x hx.right
    obtain ⟨bVx, hbVx1, hbVx2, hbVx3⟩ := open_V
    have w : ∃ bUVx ∈ B.Basics, x ∈ bUVx ∧ bUVx ⊆ bUx ∩ bVx := by
      apply B.Basis_inter
      · exact hbUx1
      · exact hbVx1
      · exact ⟨hbUx2, hbVx2⟩
    obtain ⟨bUVx, hbUVx1, hbUVx2, hbUVx3⟩ := w
    have z : bUVx ⊆ U ∩ V := by
      sorry
    use bUVx
  Open_sUnion := by
    intro S hS x hx
    rw [mem_sUnion] at hx
    obtain ⟨Ux, hUx1, hUx2⟩ := hx
    specialize hS Ux hUx1 x hUx2
    obtain ⟨bx, hbx1, hbx2, hbx3⟩ := hS
    have w : bx ⊆ ⋃₀S := by
      intro y hy
      specialize hbx3 hy
      rw [mem_sUnion]
      use Ux
    use bx

def IsBasis [Topology X] : Prop :=
  (∀ b ∈ B.Basics, Open b) ∧
  (∀ U, Open U → ∃ C ⊆ B.Basics, U = ⋃₀C)

theorem IsBasis_basisTopology : @IsBasis X B basisTopology := by
  sorry
