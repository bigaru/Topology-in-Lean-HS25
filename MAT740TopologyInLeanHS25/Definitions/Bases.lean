import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u
open Set

class Basis (X : Type u) : Type u where
  Basics : Set (Set X)
  Basis_cover : ⋃₀Basics = univ
  Basis_inter : ∀ b1 ∈ Basics, ∀ b2 ∈ Basics, ∀ x ∈ b1 ∩ b2, ∃ b3 ∈ Basics, x ∈ b3 ∧ b3 ⊆ b1 ∩ b2

variable {X : Type u} [B : Basis X]

@[simp]
theorem Basis_cover : ⋃₀B.Basics = univ := B.Basis_cover

theorem Basis_cover_x (x : X) : ∃ Bx ∈ B.Basics, x ∈ Bx := by
  by_contra c
  have w : ∃ Bx ∈ B.Basics, x ∈ Bx := by
    rw [← mem_sUnion, Basis_cover]
    trivial
  contradiction

theorem Basis_inter :
  ∀ b1 ∈ B.Basics, ∀ b2 ∈ B.Basics, ∀ x ∈ b1 ∩ b2, ∃ b3 ∈ B.Basics, x ∈ b3 ∧ b3 ⊆ b1 ∩ b2 :=
    B.Basis_inter

instance basisTopology : Topology X where
  Open := fun U ↦ ∀ x ∈ U, ∃ Bx ∈ B.Basics, x ∈ Bx ∧ Bx ⊆ U
  Open_univ := by
    intro x hx
    simp only [subset_univ, and_true]
    apply Basis_cover_x
  Open_inter := by
    intro U V hU hV x hx
    specialize hU x hx.left
    specialize hV x hx.right
    obtain ⟨BxU, hBxU1, hBxU2, hBxU3⟩ := hU
    obtain ⟨BxV, hBxV1, hBxV2, hBxV3⟩ := hV
    have w1 : ∃ BxUV ∈ B.Basics, x ∈ BxUV ∧ BxUV ⊆ BxU ∩ BxV := by
      apply Basis_inter
      · exact hBxU1
      · exact hBxV1
      · exact ⟨hBxU2, hBxV2⟩
    obtain ⟨BxUV, hBxUV1, hBxUV2, hBxUV3⟩ := w1
    have w2 : BxU ∩ BxV ⊆ U ∩ V := inter_subset_inter hBxU3 hBxV3
    have w3 : BxUV ⊆ U ∩ V := by
      intro y hy; apply w2; apply hBxUV3; exact hy
    use BxUV
  Open_sUnion := by
    intro S hS x hx
    rw [mem_sUnion] at hx
    obtain ⟨Ux, hUx1, hUx2⟩ := hx
    specialize hS Ux hUx1 x hUx2
    obtain ⟨Bx, hBx1, hBx2, hBx3⟩ := hS
    have w : Bx ⊆ ⋃₀S := by
      intro y hy
      specialize hBx3 hy
      rw [mem_sUnion]
      use Ux
    use Bx

def IsBasis [Topology X] : Prop :=
  (∀ b ∈ B.Basics, Open b) ∧
  (∀ U, Open U → ∃ C ⊆ B.Basics, U = ⋃₀ C)

theorem IsBasis_basisTopology : @IsBasis X B basisTopology := by
  constructor
  case left =>
    intro Bx hBx x hx
    use Bx
  case right =>
    intro U open_U
    have w : ∀ x ∈ U, ∃ Bx ∈ B.Basics, x ∈ Bx ∧ Bx ⊆ U := open_U
    set C := {Bx ∈ B.Basics | Bx ⊆ U}
    use C
    constructor
    case left =>
      intro y hy
      exact hy.1
    case right =>
      ext y; constructor
      case mp =>
        intro hy
        rw [mem_sUnion]
        specialize w y hy
        obtain ⟨Bx,hBx1, hBx2, hBx3⟩ := w
        have z : Bx ∈ C := by
          rw [mem_setOf]
          constructor
          case left => exact hBx1
          case right => exact hBx3
        use Bx
      case mpr =>
        intro hy
        rw [mem_sUnion] at hy
        obtain ⟨By, hBy1, hBy2⟩ := hy
        apply hBy1.right
        exact hBy2
