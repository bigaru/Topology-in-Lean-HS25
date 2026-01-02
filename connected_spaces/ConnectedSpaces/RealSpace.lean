import Mathlib.Tactic
import ConnectedSpaces.Definitions.Connectedness
import ConnectedSpaces.Definitions.NewSpaces

namespace MyReal
open Constructions

instance realTopology : Topology ℝ := @basisTopology ℝ metricBasis

@[simp]
def Interval (A : Set ℝ) : Prop :=
  ∀ {a b z : ℝ}, a ∈ A → b ∈ A → a ≤ z → z ≤ b → z ∈ A

instance subsetTopology (A : Set ℝ) : Topology {x : ℝ // x ∈ A} :=
  pullbackTopology ℝ realTopology {x : ℝ // x ∈ A} Subtype.val

@[simp]
lemma open_Iio (z : ℝ) : Open {x : ℝ | x < z} := by
  apply (Open_basisTopology (B := metricBasis)).2
  intro x hx
  have hxz : x < z := hx
  set ε := z - x with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact sub_pos.mpr hxz
  refine ⟨Metric.ball x ε, ?_, ?_, ?_⟩
  · exact Basic_balls
  · simp [Metric.ball, hε, ε]
  · intro y hy
    have hy' : |y - x| < ε := by
      have hy1 : dist y x < ε := hy
      have hdist : dist y x = |y - x| := by
        simp [Real.dist_eq]
      rw [hdist] at hy1
      exact hy1
    have hy_lt : y - x < ε := (abs_lt.mp hy').2
    have : y < z := by
      have hy2 := hy_lt
      rw [hεdef] at hy2
      linarith
    exact this

@[simp]
lemma open_Ioi (z : ℝ) : Open {x : ℝ | z < x} := by
  apply (Open_basisTopology (B := metricBasis)).2
  intro x hx
  have hzx : z < x := hx
  set ε := x - z with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact sub_pos.mpr hzx
  refine ⟨Metric.ball x ε, ?_, ?_, ?_⟩
  · exact Basic_balls
  · simp [Metric.ball, hε, ε]
  · intro y hy
    have hy' : |y - x| < ε := by
      have hy1 : dist y x < ε := hy
      have hdist : dist y x = |y - x| := by
        simp [Real.dist_eq]
      rw [hdist] at hy1
      exact hy1
    have hy_gt : -ε < y - x := (abs_lt.mp hy').1
    have : z < y := by
      have hy2 := hy_gt
      rw [hεdef] at hy2
      linarith
    exact this

end MyReal
