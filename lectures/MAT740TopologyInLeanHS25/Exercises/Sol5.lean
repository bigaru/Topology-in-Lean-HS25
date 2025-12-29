import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Bases

universe u v
variable {X : Type u} {Y : Type v}

/- # Problem 1 (4 points) -/
section Problem1
variable [Topology X] [BY : Basis Y]

theorem Cont_Basics' (f : X → Y) : Cont f ↔ ∀ b ∈ BY.Basics, Open (f ⁻¹' b) := by
  constructor
  case mp =>
    intro cont_f b basic_b
    apply cont_f
    exact Open_Basics b basic_b
  case mpr =>
    intro h U open_U
    have w : ∃ C ⊆ BY.Basics, U = ⋃₀ C :=
      IsBasis_basisTopology.right U open_U
    obtain ⟨C, hC1, hC2⟩ := w
    rw [hC2]
    rw [Set.preimage_sUnion, ← Set.sUnion_image]
    apply Open_sUnion
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro V hV
    apply hC1 at hV
    exact h V hV

end Problem1

/- # Problem 2 (6 points) -/
section Problem2
open Metric
variable [MetricSpace X]


/- (a) (3 points) -/
theorem ball_in_ball' {x : X} {ε : ℝ} : ∀ y ∈ ball x ε, ∃ δ, (0 < δ ∧ ball y δ ⊆ ball x ε) := by
  simp only [ball, Set.setOf_subset_setOf]
  intro y hy
  simp at hy
  use ε - (dist y x)
  constructor
  case left =>
    linarith
  case right =>
    intro z hz
    have hzyx : dist z y + dist y x < ε := by
      linarith
    have triangle : dist z x ≤ dist z y + dist y x := by
      apply dist_triangle
    linarith

/- (b) (3 points) -/
instance metricBasis' : Basis X where
  Basics := {B | ∃ x ε, B = ball x ε}
  Basis_cover := by
    rw [Set.sUnion_eq_univ_iff]
    intro a
    use Metric.ball a 1
    simp only [Set.mem_setOf_eq, exists_apply_eq_apply2', mem_ball, dist_self, zero_lt_one,
      and_self]
  Basis_inter := by
    /- No need to prove this! -/
    sorry

end Problem2
