import Mathlib.Tactic
import ConnectedSpaces.Definitions.Connectedness

open Set

open MyConnected

instance realTopology : Topology ℝ := @basisTopology ℝ metricBasis



def Interval (A : Set ℝ) : Prop :=
  /- Assuming a ≤ b -/
  ∀ {a b x : ℝ}, a ∈ A → b ∈ A → a ≤ x → x ≤ b → x ∈ A


/- Similarly for others Ioo, Ico, Ioc -/
example : Interval (Set.Icc 0 1) := by
  intro a b x ha hb hax hxb
  repeat rw [Set.mem_Icc] at ha hb
  constructor
  · linarith
  · linarith


lemma open_Iio (x : ℝ) : Open (Set.Iio x) := by
  refine
    (Open_basisTopology (B := metricBasis) (U := Set.Iio x)).2 ?_
  intro y hy
  have hyx : y < x := hy
  refine ⟨Metric.ball y ((x - y) / 2), ?_⟩
  constructor
  · exact Basic_balls
  constructor
  · have : 0 < (x - y) / 2 := by
      have : 0 < x - y := sub_pos.mpr hyx
      exact half_pos this
    simp [Metric.mem_ball, dist_self, this]
  · intro z hz
    have hz' : dist z y < (x - y) / 2 := by
      simpa [Metric.mem_ball] using hz
    have hz_abs : |z - y| < (x - y) / 2 := by
      simpa [Real.dist_eq] using hz'
    have hz_mid : z < y + (x - y) / 2 := by
      have hz_diff : z - y < (x - y) / 2 := (abs_lt.mp hz_abs).2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hz_diff y
    have mid_lt_x : y + (x - y) / 2 < x := by
      have : y < x := hyx
      linarith
    have hz_lt : z < x := lt_trans hz_mid mid_lt_x
    simpa [Set.mem_Iio] using hz_lt


lemma open_Ioi (x : ℝ) : Open (Set.Ioi x) := by
  refine
    (Open_basisTopology (B := metricBasis) (U := Set.Ioi x)).2 ?_
  intro y hy
  have hxy : x < y := hy
  refine ⟨Metric.ball y ((y - x) / 2), ?_⟩
  constructor
  · exact Basic_balls
  constructor
  · have : 0 < (y - x) / 2 := by
      have : 0 < y - x := sub_pos.mpr hxy
      exact half_pos this
    simp [Metric.mem_ball, dist_self, this]
  · intro z hz
    have hz' : dist z y < (y - x) / 2 := by
      simpa [Metric.mem_ball] using hz
    have hz_abs : |z - y| < (y - x) / 2 := by
      simpa [Real.dist_eq] using hz'
    have hz_shift : y - (y - x) / 2 < z := by
      have := add_lt_add_left ((abs_lt.mp hz_abs).1) y
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have mid_eq : y - (y - x) / 2 = (x + y) / 2 := by ring
    have hz_gt_mid : (x + y) / 2 < z := by simpa [mid_eq] using hz_shift
    have mid_gt_x : x < (x + y) / 2 := by
      have : x < y := hxy
      linarith
    have hxz : x < z := lt_trans mid_gt_x hz_gt_mid
    simpa [Set.mem_Ioi] using hxz
