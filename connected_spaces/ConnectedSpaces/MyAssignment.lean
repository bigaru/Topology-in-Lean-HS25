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


theorem is_interval_connected_subset_real (A : Set ℝ) :
IsInterval A → Connected {x : ℝ // x ∈ A} := by
  intro hInterval

  -- Use the non-separation characterization of connectedness
  refine (Connected_iff_nonSep (X := {x : ℝ // x ∈ A})).2 ?_
  intro U V hdata
  rcases hdata with ⟨openU, hU_nonempty, openV, hV_nonempty, hUV_disjoint⟩

  -- It suffices to rule out a separation `U ∪ V = univ`
  intro hUnion
  rcases hU_nonempty with ⟨x0, hx0⟩
  rcases hV_nonempty with ⟨y0, hy0⟩

  -- If the first chosen points are in the opposite order, swap the roles of `U` and `V`
  have hswap : ∀
      (U V : Set {x : ℝ // x ∈ A})
      (openU : Open U) (openV : Open V)
      (hU_nonempty : U.Nonempty) (hV_nonempty : V.Nonempty)
      (hUV_disjoint : Disjoint U V) (hUnion : U ∪ V = Set.univ)
      (x y : {x : ℝ // x ∈ A}) (hxU : x ∈ U) (hyV : y ∈ V) (hxy : x.val < y.val), False := by
    intro U V openU openV hU_nonempty hV_nonempty hUV_disjoint hUnion x y hx hy hxy

    -- Real-valued shadow of the left piece: U' = [x,y) ∩ U (projected to ℝ)
    let U' : Set ℝ := {t : ℝ | x.val ≤ t ∧ t < y.val ∧ ∃ u ∈ U, u.val = t}

    have hx_mem : x.val ∈ U' := by exact ⟨le_rfl, hxy, ⟨x, hx, rfl⟩⟩
    have hU'_nonempty : U'.Nonempty := ⟨x.val, hx_mem⟩
    have hU'_bdd : BddAbove U' := ⟨y.val, by intro t ht; exact le_of_lt ht.2.1⟩

    -- Define s = sup U'
    let s : ℝ := sSup U'
    have hs_ge_x : x.val ≤ s := le_csSup hU'_bdd hx_mem
    have hs_le_y : s ≤ y.val := csSup_le hU'_nonempty (by intro t ht; exact le_of_lt ht.2.1)

    -- s lies in A by the interval property
    have hs_inA : s ∈ A := hInterval x.property y.property hs_ge_x hs_le_y
    let sSub : {x : ℝ // x ∈ A} := ⟨s, hs_inA⟩

    -- Every point belongs to U ∪ V
    have hs_union : sSub ∈ U ∪ V := by simpa [hUnion] using (by trivial : sSub ∈ Set.univ)

    -- Unpack the subspace openness data
    rcases openU with ⟨U0, hU0_open, hU_eq⟩
    rcases openV with ⟨V0, hV0_open, hV_eq⟩

    -- Neighborhoods of s in ℝ coming from U or V
    have hs_cases : (sSub ∈ U) ∨ (sSub ∈ V) := by
      simpa using hs_union

    -- Case 1: s ∈ U, build a point of U' above s
    have hU_case : sSub ∈ U → False := by
      intro hsU
      have hsU0 : s ∈ U0 := by simpa [hU_eq] using hsU
      -- Choose a metric ball around s contained in U0
      obtain ⟨B, hB_basic, hsB, hB_subset⟩ :=
        (Open_basisTopology (B := metricBasis)).1 hU0_open s hsU0
      rcases hB_basic with ⟨c, ε, rfl⟩
      obtain ⟨δ, hδpos, hδ_sub⟩ := ball_in_ball (x := c) (ε := ε) (y := s) hsB
      have hBall_subset_U0 : Metric.ball s δ ⊆ U0 := by
        intro t ht
        apply hB_subset
        exact hδ_sub ht

      -- We need room on the right of s (since y ∈ V, s ≠ y)
      have hs_ne_y : s ≠ y.val := by
        intro h
        have hy_inU : (y : {x : ℝ // x ∈ A}) ∈ U := by
          have hyU0 : y.val ∈ U0 := by simpa [h] using hsU0
          simpa [hU_eq] using hyU0
        exact (Set.disjoint_left.mp hUV_disjoint) hy_inU hy

      have hgap : 0 < (y.val - s) := sub_pos.mpr (lt_of_le_of_ne hs_le_y hs_ne_y)

      -- Pick a smaller radius δ' so that s + δ' < y and the ball stays in U0
      let δ' : ℝ := min δ ((y.val - s) / 2)
      have hδ'_pos : 0 < δ' := by
        apply lt_min hδpos
        nlinarith
      have hδ'_le : δ' ≤ δ := min_le_left _ _
      have hBall_subset_U0' : Metric.ball s δ' ⊆ U0 := by
        have hsubset : Metric.ball s δ' ⊆ Metric.ball s δ :=
          Metric.ball_subset_ball hδ'_le
        intro t ht
        exact hBall_subset_U0 (hsubset ht)

      -- Choose a point just to the right of s that stays inside (s + δ') and hence in U
      set t := s + δ' / 2 with ht_def
      have ht_gt_s : s < t := by
        have : (0 : ℝ) < δ' := hδ'_pos
        nlinarith [ht_def]
      have ht_lt_y : t < y.val := by
        have hδ'_le' : δ' ≤ (y.val - s) / 2 := min_le_right _ _
        have ht_le_mid : t ≤ s + (y.val - s) / 2 := by nlinarith [ht_def, hδ'_le']
        have hmid_lt : s + (y.val - s) / 2 < y.val := by nlinarith
        exact lt_of_le_of_lt ht_le_mid hmid_lt

      -- t belongs to A (interval property) and to U
      have ht_inA : t ∈ A :=
        hInterval x.property y.property (by nlinarith [hs_ge_x]) (le_of_lt ht_lt_y)
      have ht_in_ball : t ∈ Metric.ball s δ' := by
        -- Compute the distance explicitly: |t - s| = δ'/2
        have hts : t - s = δ' / 2 := by
          simp [ht_def]
        have hdist : |t - s| = δ' / 2 := by
          have hδ'_nonneg : 0 ≤ δ' := le_of_lt hδ'_pos
          have hδ'half_nonneg : 0 ≤ δ' / 2 := by nlinarith
          calc
            |t - s| = |δ' / 2| := by simpa [hts]
            _ = δ' / 2 := abs_of_nonneg hδ'half_nonneg
        have : |t - s| < δ' := by nlinarith [hdist, hδ'_pos]
        simpa [Metric.ball, Real.dist_eq] using this
      have ht_inU0 : t ∈ U0 := hBall_subset_U0' ht_in_ball
      have ht_inU : (⟨t, ht_inA⟩ : {x : ℝ // x ∈ A}) ∈ U := by
        simpa [hU_eq] using ht_inU0

      -- t witnesses that s is not an upper bound of U'
      have ht_mem_U' : t ∈ U' := by
        refine ⟨?_, ht_lt_y, ?_⟩
        · nlinarith [hs_ge_x]
        · refine ⟨⟨t, ht_inA⟩, ht_inU, rfl⟩

      have ht_le_s : t ≤ s := le_csSup hU'_bdd ht_mem_U'
      have hcontr : s < s := lt_of_lt_of_le ht_gt_s ht_le_s
      exact (lt_irrefl _ ) hcontr

    -- Case 2: s ∈ V, show s − δ is a smaller upper bound
    have hV_case : sSub ∈ V → False := by
      intro hsV
      have hsV0 : s ∈ V0 := by simpa [hV_eq] using hsV
      obtain ⟨B, hB_basic, hsB, hB_subset⟩ :=
        (Open_basisTopology (B := metricBasis)).1 hV0_open s hsV0
      rcases hB_basic with ⟨c, ε, rfl⟩
      obtain ⟨δ, hδpos, hδ_sub⟩ := ball_in_ball (x := c) (ε := ε) (y := s) hsB
      have hBall_subset_V0 : Metric.ball s δ ⊆ V0 := by
        intro t ht
        apply hB_subset
        exact hδ_sub ht

      -- Here we need room on the left of s (otherwise x ∈ V contradicts disjointness)
      have hs_ne_x : s ≠ x.val := by
        intro h
        have hx_inV : (x : {x : ℝ // x ∈ A}) ∈ V := by
          have hxV0 : x.val ∈ V0 := by simpa [h] using hsV0
          simpa [hV_eq] using hxV0
        exact (Set.disjoint_left.mp hUV_disjoint) hx hx_inV
      have hgap_left : 0 < s - x.val := sub_pos.mpr (lt_of_le_of_ne hs_ge_x hs_ne_x.symm)

      let δ' : ℝ := min δ ((s - x.val) / 2)
      have hδ'_pos : 0 < δ' := by
        apply lt_min hδpos
        nlinarith
      have hδ'_le : δ' ≤ δ := min_le_left _ _
      have hBall_subset_V0' : Metric.ball s δ' ⊆ V0 := by
        have hsubset : Metric.ball s δ' ⊆ Metric.ball s δ :=
          Metric.ball_subset_ball hδ'_le
        intro t ht
        exact hBall_subset_V0 (hsubset ht)

      -- Show s - δ' is an upper bound, contradicting minimality of s
      have hUpper : ∀ t ∈ U', t ≤ s - δ' := by
        intro t ht
        have ht_le_s : t ≤ s := le_csSup hU'_bdd ht
        by_contra hnot
        have ht_gt : t > s - δ' := not_le.mp hnot
        have ht_in_ball : t ∈ Metric.ball s δ' := by
          -- Since t ≤ s and t > s - δ', we have |t - s| = s - t < δ'
          have hts_nonpos : t - s ≤ 0 := sub_nonpos.mpr ht_le_s
          have hdist : |t - s| = s - t := by
            have habs := abs_of_nonpos hts_nonpos
            nlinarith [habs]
          have hst_lt : s - t < δ' := by nlinarith
          have : |t - s| < δ' := by nlinarith [hdist, hst_lt]
          simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using this
        have ht_inV0 : t ∈ V0 := hBall_subset_V0' ht_in_ball
        rcases ht.2.2 with ⟨u, huU, hval⟩
        have huV : (u : {x : ℝ // x ∈ A}) ∈ V := by simpa [hV_eq, hval] using ht_inV0
        exact (Set.disjoint_left.mp hUV_disjoint) huU huV

      have hNewUpper : s ≤ s - δ' := csSup_le hU'_nonempty hUpper
      have : (0 : ℝ) < δ' := hδ'_pos
      linarith

    obtain hU | hV  := hs_cases
    · exact hU_case hU
    · exact hV_case hV

  -- Apply the main argument to the correctly ordered pair of witnesses
  have hlt_or_gt : x0.val < y0.val ∨ y0.val < x0.val := lt_or_gt_of_ne (by
    intro h
    apply (Set.disjoint_left.mp hUV_disjoint) hx0
    simpa [Subtype.ext h] using hy0)

  cases hlt_or_gt with
  | inl hlt =>
      exact hswap U V openU openV ⟨x0, hx0⟩ ⟨y0, hy0⟩ hUV_disjoint hUnion x0 y0 hx0 hy0 hlt
  | inr hlt =>
      have hUnion' : V ∪ U = Set.univ := by simpa [Set.union_comm] using hUnion
      exact hswap V U openV openU ⟨y0, hy0⟩ ⟨x0, hx0⟩ hUV_disjoint.symm hUnion' y0 x0 hy0 hx0 hlt
