import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Bases

universe u v
variable {X : Type u} {Y : Type v}

/- # Problem 1 (4 points) -/
section Problem1
variable [Topology X] [BY : Basis Y]

theorem Cont_Basics' (f : X → Y) : Cont f ↔ ∀ b ∈ BY.Basics, Open (f ⁻¹' b) := by
  /-
    (=>) use `Open_Basics`
    (<=) use `IsBasis_basisTopology` to decompose open U into union of basis element.
    Then use properties of preimages `Set.preimage_sUnion` and `Set.sUnion_image`.
  -/
  sorry

end Problem1

/- # Problem 2 (6 points) -/
section Problem2
open Metric
variable [MetricSpace X]


/- (a) (3 points) -/
theorem ball_in_ball' {x : X} {ε : ℝ} : ∀ y ∈ ball x ε, ∃ δ, (0 < δ ∧ ball y δ ⊆ ball x ε) := by
  sorry
  /-
  use `linarith` and `dist_triangle`
  -/

/- (b) (3 points) -/
instance metricBasis' : Basis X where
  Basics := {B | ∃ x ε, B = ball x ε}
  Basis_cover := by
    sorry
    /-
    Prove this!
    use `simp?` here to get a short proof
    -/
  Basis_inter := by
    /- No need to prove this! -/
    sorry

end Problem2
