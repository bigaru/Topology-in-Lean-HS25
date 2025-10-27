import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Bases

universe u v
variable {X : Type u} {Y : Type v}

/- # Problem 1 (4 points) -/
section Problem1
variable [Topology X] [BY : Basis Y]

/-
  (=>) use `Open_Basics`
  (<=) use `IsBasis_basisTopology` to decompose open U into union of basis element.
  Then use properties of preimages `Set.preimage_sUnion` and `Set.sUnion_image`.
-/
theorem Cont_Basics' (f : X → Y) : Cont f ↔ ∀ b ∈ BY.Basics, Open (f ⁻¹' b) := by
  constructor
  · intro hf b hb
    apply hf b
    apply Open_Basics
    exact hb

  · intro hU U open_U
    have w : ∃ C ⊆ BY.Basics, U = ⋃₀ C := by
      apply IsBasis_basisTopology.2
      exact open_U

    rcases w with ⟨C, hC, rfl⟩
    rw [Set.preimage_sUnion, ← Set.sUnion_image]
    apply Open_sUnion

    rintro _ ⟨b, hbC, rfl⟩
    exact hU b (hC hbC)

end Problem1

/- # Problem 2 (6 points) -/
section Problem2
open Metric
variable [MetricSpace X]


/- (a) (3 points) -/
/-
  use `linarith` and `dist_triangle`
-/
theorem ball_in_ball' {x : X} {ε : ℝ} : ∀ y ∈ ball x ε, ∃ δ, (0 < δ ∧ ball y δ ⊆ ball x ε) := by
  intro y hy
  let δ := ε - dist x y
  rw [mem_ball, dist_comm] at hy

  use δ
  constructor
  · rw [← sub_pos] at hy
    exact hy

  · intro z hz
    rw [mem_ball, dist_comm] at hz
    rw [mem_ball, dist_comm]

    have htriangle: dist x z ≤ dist x y + dist y z := dist_triangle x y z
    linarith

/- (b) (3 points) -/
instance metricBasis' : Basis X where
  Basics := {B | ∃ x ε, B = ball x ε}
  Basis_cover := by
    /-
    Prove this!
    use `simp?` here to get a short proof
    -/
    ext y
    constructor
    · intro hy
      simp only [Set.mem_univ]

    · intro h1
      simp only [Set.mem_sUnion, Set.mem_setOf_eq]
      use ball y 1
      constructor
      · use y, 1
      · simp only [mem_ball, dist_self, zero_lt_one]

  Basis_inter := by
    /- No need to prove this! -/
    sorry

end Problem2
