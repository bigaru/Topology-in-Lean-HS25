import Mathlib.Tactic
import ConnectedSpaces.Definitions.Connectedness
import ConnectedSpaces.Definitions.NewSpaces

open Set

open MyConnected
open Constructions

instance realTopology : Topology ℝ := @basisTopology ℝ metricBasis

def IsInterval (A : Set ℝ) : Prop :=
  ∀ {a b z : ℝ}, a ∈ A → b ∈ A → a ≤ z → z ≤ b → z ∈ A

instance subsetTopology (A : Set ℝ) : Topology {x : ℝ // x ∈ A} :=
  pullbackTopology ℝ realTopology {x : ℝ // x ∈ A} Subtype.val

lemma open_Iio (z : ℝ) : Open {x : ℝ | x < z} := by
  classical
  refine (Open_basisTopology (B := metricBasis)).2 ?_
  intro x hx
  have hxz : x < z := hx
  set ε := z - x with hεdef
  have hε : 0 < ε := by
    simpa [ε, hεdef, sub_eq_add_neg] using sub_pos.mpr hxz
  refine ⟨Metric.ball x ε, ?_, ?_, ?_⟩
  · exact Basic_balls
  · simp [Metric.ball, hε, ε]
  · intro y hy
    have hy' : |y - x| < ε := by
      simpa [Metric.ball, Real.dist_eq, ε, hεdef, abs_sub_comm] using hy
    have hy_lt : y - x < ε := (abs_lt.mp hy').2
    have : y < z := by
      have := add_lt_add_right hy_lt x
      simpa [ε, hεdef, add_comm, add_left_comm, add_assoc, add_sub_cancel, sub_eq_add_neg]
      using this
    exact this

lemma open_Ioi (z : ℝ) : Open {x : ℝ | z < x} := by
  classical
  refine (Open_basisTopology (B := metricBasis)).2 ?_
  intro x hx
  have hzx : z < x := hx
  set ε := x - z with hεdef
  have hε : 0 < ε := by
    simpa [ε, hεdef, sub_eq_add_neg] using sub_pos.mpr hzx
  refine ⟨Metric.ball x ε, ?_, ?_, ?_⟩
  · exact Basic_balls
  · simp [Metric.ball, hε, ε]
  · intro y hy
    have hy' : |y - x| < ε := by
      simpa [Metric.ball, Real.dist_eq, ε, hεdef, abs_sub_comm] using hy
    have hy_gt : -ε < y - x := (abs_lt.mp hy').1
    have : z < y := by
      have := add_lt_add_right hy_gt x
      have hxz : x - ε = z := by
        simp [ε]
      simpa [ε, hεdef, hxz, add_comm, add_left_comm, add_assoc, add_sub_cancel, sub_eq_add_neg]
      using this
    exact this



theorem connected_subset_real_is_interval (A : Set ℝ) :
Connected {x : ℝ // x ∈ A} → IsInterval A := by
  intro hconn a b z ha hb haz hzb
  by_contra hznot

  -- U = A ∩ (-∞, z), V = A ∩ (z, ∞)
  let U : Set {x : ℝ // x ∈ A} := {x | x.val < z}
  let V : Set {x : ℝ // x ∈ A} := {x | z < x.val}

  -- U and V are open in the subspace topology
  have openU : Open U := by
    use Set.Iio z
    exact ⟨open_Iio z, rfl⟩

  have openV : Open V := by
    use Set.Ioi z
    exact ⟨open_Ioi z, rfl⟩

  -- U, V are nonempty (a < z and z < b)
  have hneq_a : a ≠ z := by
    intro h
    apply hznot
    rw [h] at ha
    exact ha
  have hneq_b : b ≠ z := by
    intro h
    apply hznot
    rw [h] at hb
    exact hb

  have ha_lt_z : a < z := lt_of_le_of_ne haz hneq_a
  have hz_lt_b : z < b := lt_of_le_of_ne hzb hneq_b.symm

  have hU_nonempty : U.Nonempty := by refine ⟨⟨a, ha⟩, ha_lt_z⟩
  have hV_nonempty : V.Nonempty := by refine ⟨⟨b, hb⟩, hz_lt_b⟩

  -- U and V are disjoint
  have hUV_disjoint : Disjoint U V := by
    refine disjoint_left.mpr ?_
    intro x hxU hxV
    have hxU' : x.val < z := hxU
    have hxV' : z < x.val := hxV
    exact (lt_asymm hxU' hxV').elim

  -- Every point of A lies in U or V since z ∉ A
  have hUnion : U ∪ V = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hxA : x.val ∈ A := x.property
    have hx_ne_z : x.val ≠ z := by
      intro h
      apply hznot
      rw [h] at hxA
      exact hxA

    have hx_lt_or_gt : x.val < z ∨ z < x.val := lt_or_gt_of_ne hx_ne_z
    obtain hxlt|hxgt := hx_lt_or_gt
    · left
      exact hxlt
    · right
      exact hxgt

  -- Contradiction with connectedness
  have hSep : U ∪ V ≠ Set.univ :=
    (Connected_iff_nonSep.mp hconn) U V ⟨openU, hU_nonempty, openV, hV_nonempty, hUV_disjoint⟩
  exact hSep hUnion
