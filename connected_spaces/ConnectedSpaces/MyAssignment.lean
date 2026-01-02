import Mathlib.Tactic
import ConnectedSpaces.Definitions.ContinuousFunctions
import ConnectedSpaces.Definitions.Connectedness
import ConnectedSpaces.Definitions.NewSpaces
import ConnectedSpaces.RealSpace


open MyConnected
open MyReal


theorem connected_real_subset_implies_interval {A : Set ℝ} :
Connected {x : ℝ // x ∈ A} → Interval A := by
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
    refine Set.disjoint_left.mpr ?_
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


theorem interval_implies_connected_real_subset {A : Set ℝ} :
Interval A → Connected {x : ℝ // x ∈ A} := by
  intro hInterval

  -- Prove connectedness via the non-separation characterization.
  refine (Connected_iff_nonSep (X := {x : ℝ // x ∈ A})).2 ?_
  intro U V hdata
  rcases hdata with ⟨openU, hU_nonempty, openV, hV_nonempty, hUV_disjoint⟩
  intro hUnion
  rcases hU_nonempty with ⟨x, hxU⟩
  rcases hV_nonempty with ⟨y, hyV⟩

  -- Core supremum argument for a fixed ordered pair x < y.
  have sep_contra :
      ∀ (U V : Set {x : ℝ // x ∈ A}),
        Open U → Open V → Disjoint U V → U ∪ V = Set.univ →
        ∀ (x y : {x : ℝ // x ∈ A}), x ∈ U → y ∈ V → x.val < y.val → False := by
    intro U V openU openV disjUV unionUV x y hx hy hxy

    -- Real-valued shadow of the left piece: U' = [x,y) ∩ image(U)
    let U' : Set ℝ := {t : ℝ | x.val ≤ t ∧ t < y.val ∧ ∃ u ∈ U, u.val = t}
    have hx_mem : x.val ∈ U' := ⟨le_rfl, hxy, ⟨x, hx, rfl⟩⟩
    have hU'_nonempty : U'.Nonempty := ⟨x.val, hx_mem⟩
    have hU'_bdd : BddAbove U' := ⟨y.val, by
      intro t ht
      exact le_of_lt ht.2.1⟩

    let s : ℝ := sSup U'
    have hs_ge_x : x.val ≤ s := le_csSup hU'_bdd hx_mem
    have hs_le_y : s ≤ y.val := csSup_le hU'_nonempty (by
      intro t ht
      exact le_of_lt ht.2.1)

    have hs_inA : s ∈ A := hInterval x.property y.property hs_ge_x hs_le_y
    let sSub : {x : ℝ // x ∈ A} := ⟨s, hs_inA⟩

    have hs_union : sSub ∈ U ∪ V := by simp [unionUV]
    rcases openU with ⟨U0, hU0_open, hU_eq⟩
    rcases openV with ⟨V0, hV0_open, hV_eq⟩

    have hU_case : sSub ∈ U → False := by
      intro hsU
      have hsU0 : s ∈ U0 := by rw [hU_eq] at hsU; exact hsU

      -- y cannot coincide with s, otherwise y ∈ U ∩ V
      have hs_ne_y : s ≠ y.val := by
        intro hsy
        have hyU0 : y.val ∈ U0 := by rw [hsy] at hsU0; exact hsU0
        have hy_inU : (y : {x : ℝ // x ∈ A}) ∈ U := by rw [hU_eq];exact hyU0
        exact (Set.disjoint_left.mp disjUV) hy_inU hy
      have hgap : 0 < y.val - s := sub_pos.mpr (lt_of_le_of_ne hs_le_y hs_ne_y)

      -- Openness gives a small ball around s contained in U0
      obtain ⟨B, hB_basic, hsB, hB_subset⟩ :=
        (Open_basisTopology (B := metricBasis)).1 hU0_open s hsU0
      rcases hB_basic with ⟨c, ε, rfl⟩
      obtain ⟨δ, hδpos, hδ_sub⟩ := ball_in_ball (x := c) (ε := ε) (y := s) hsB
      have hBall_subset_U0 : Metric.ball s δ ⊆ U0 := by
        intro t ht
        apply hB_subset
        exact hδ_sub ht

      let δ' : ℝ := min δ ((y.val - s) / 2)
      have hδ'_pos : 0 < δ' := by
        apply lt_min hδpos
        nlinarith [hgap]
      have hδ'_le : δ' ≤ δ := min_le_left _ _
      have hBall_subset_U0' : Metric.ball s δ' ⊆ U0 := by
        have hsubset : Metric.ball s δ' ⊆ Metric.ball s δ :=
          Metric.ball_subset_ball hδ'_le
        intro t ht
        exact hBall_subset_U0 (hsubset ht)

      set t : ℝ := s + δ' / 2 with ht_def
      have ht_gt_s : s < t := by nlinarith [ht_def, hδ'_pos]
      have ht_lt_y : t < y.val := by
        have hδ'_le' : δ' ≤ (y.val - s) / 2 := min_le_right _ _
        have ht_le_mid : t ≤ s + (y.val - s) / 4 := by nlinarith [ht_def, hδ'_le']
        have hmid_lt : s + (y.val - s) / 4 < y.val := by nlinarith [hgap]
        exact lt_of_le_of_lt ht_le_mid hmid_lt

      have ht_inA : t ∈ A :=
        hInterval x.property y.property (le_trans hs_ge_x (le_of_lt ht_gt_s)) (le_of_lt ht_lt_y)

      have ht_in_ball : t ∈ Metric.ball s δ' := by
        have hts : t - s = δ' / 2 := by simp [ht_def]
        have hhalf_pos : 0 < δ' / 2 := by nlinarith [hδ'_pos]
        have habs : |t - s| = δ' / 2 := by
          calc
            |t - s| = |δ' / 2| := by simp [hts]
            _ = δ' / 2 := abs_of_nonneg (le_of_lt hhalf_pos)
        have : |t - s| < δ' := by nlinarith [habs, hδ'_pos]
        apply this

      have ht_inU0 : t ∈ U0 := hBall_subset_U0' ht_in_ball
      have ht_inU : (⟨t, ht_inA⟩ : {x : ℝ // x ∈ A}) ∈ U := by rw [hU_eq]; exact ht_inU0

      have ht_mem_U' : t ∈ U' := by
        refine ⟨le_trans hs_ge_x (le_of_lt ht_gt_s), ht_lt_y, ?_⟩
        exact ⟨⟨t, ht_inA⟩, ht_inU, rfl⟩

      have ht_le_s : t ≤ s := le_csSup hU'_bdd ht_mem_U'
      exact (not_lt_of_ge ht_le_s) ht_gt_s

    have hV_case : sSub ∈ V → False := by
      intro hsV
      have hsV0 : s ∈ V0 := by simp [hV_eq] at hsV; exact hsV

      -- x cannot coincide with s, otherwise x ∈ U ∩ V
      have hs_ne_x : s ≠ x.val := by
        intro hsx
        have hx_eq : x = sSub := by
          ext
          simp [sSub, hsx]
        have hx_inV : x ∈ V := by rw [← hx_eq] at hsV; exact hsV
        exact (Set.disjoint_left.mp disjUV) hx hx_inV
      have hgap_left : 0 < s - x.val := sub_pos.mpr (lt_of_le_of_ne hs_ge_x hs_ne_x.symm)

      obtain ⟨B, hB_basic, hsB, hB_subset⟩ :=
        (Open_basisTopology (B := metricBasis)).1 hV0_open s hsV0
      rcases hB_basic with ⟨c, ε, rfl⟩
      obtain ⟨δ, hδpos, hδ_sub⟩ := ball_in_ball (x := c) (ε := ε) (y := s) hsB
      have hBall_subset_V0 : Metric.ball s δ ⊆ V0 := by
        intro t ht
        apply hB_subset
        exact hδ_sub ht

      let δ' : ℝ := min δ ((s - x.val) / 2)
      have hδ'_pos : 0 < δ' := by
        apply lt_min hδpos
        nlinarith [hgap_left]
      have hδ'_le : δ' ≤ δ := min_le_left _ _
      have hBall_subset_V0' : Metric.ball s δ' ⊆ V0 := by
        have hsubset : Metric.ball s δ' ⊆ Metric.ball s δ :=
          Metric.ball_subset_ball hδ'_le
        intro t ht
        exact hBall_subset_V0 (hsubset ht)

      have hUpper : ∀ t ∈ U', t ≤ s - δ' := by
        intro t ht
        have ht_le_s : t ≤ s := le_csSup hU'_bdd ht
        by_contra hnot
        have ht_gt : s - δ' < t := lt_of_not_ge hnot

        have ht_in_ball : t ∈ Metric.ball s δ' := by
          have hts_nonpos : t - s ≤ 0 := sub_nonpos.mpr ht_le_s
          have habs' : |t - s| = -(t - s) := abs_of_nonpos hts_nonpos
          have habs : |t - s| = s - t := by nlinarith [habs']
          have hst_lt : s - t < δ' := by nlinarith [ht_gt]
          have : |t - s| < δ' := by nlinarith [habs, hst_lt]
          simp [Metric.ball, Real.dist_eq]
          exact this

        have ht_inV0 : t ∈ V0 := hBall_subset_V0' ht_in_ball
        rcases ht.2.2 with ⟨u, huU, hval⟩
        have huV0 : u.val ∈ V0 := by rw [← hval] at ht_inV0; exact ht_inV0
        have huV : u ∈ V := by rw [hV_eq]; exact huV0
        exact (Set.disjoint_left.mp disjUV) huU huV

      have hs_le : s ≤ s - δ' := csSup_le hU'_nonempty hUpper
      have hs_lt : s - δ' < s := by nlinarith [hδ'_pos]
      have : s < s := lt_of_le_of_lt hs_le hs_lt
      exact lt_irrefl _ this

    obtain hsU | hsV := hs_union
    · exact hU_case hsU
    · exact hV_case hsV

  -- Ensure we have an ordered pair; otherwise swap U and V.
  have hne_val : x.val ≠ y.val := by
    intro h
    have hxy_eq : x = y := by ext; exact h
    have : x ∈ V := by rw [← hxy_eq] at hyV; exact hyV
    exact (Set.disjoint_left.mp hUV_disjoint) hxU this

  obtain hxy | hyx := lt_or_gt_of_ne hne_val
  · exact sep_contra U V openU openV hUV_disjoint hUnion x y hxU hyV hxy
  · have hUnion' : V ∪ U = Set.univ := by rw [Set.union_comm] at hUnion; exact hUnion
    exact sep_contra V U openV openU hUV_disjoint.symm hUnion' y x hyV hxU hyx


theorem connected_real_subset_iff_interval {A : Set ℝ} :
Connected {x : ℝ // x ∈ A} ↔ Interval A := by
  constructor
  · exact connected_real_subset_implies_interval
  · exact interval_implies_connected_real_subset



theorem intermediate_value_theorem {f : ℝ → ℝ} {a b y : ℝ}
    (hab : a ≤ b)
    (hf : MyReal.ContinuousOn f (Set.Icc a b))
    (hy : y ∈ Set.Icc (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = y := by

  -- [a,b] is an interval set, hence its subtype is connected.
  have hInterval_domain : Interval (Set.Icc a b) := by
    intro a' b' z ha' hb' ha'z hzb'
    refine ⟨?_, ?_⟩
    · exact le_trans ha'.1 ha'z
    · exact le_trans hzb' hb'.2

  have hConn_domain : Connected {x : ℝ // x ∈ Set.Icc a b} :=
    (connected_real_subset_iff_interval (A := Set.Icc a b)).2 hInterval_domain
  -- Continuity-on gives continuity of the restriction fRes : [a,b] → ℝ.
  let fRes : {x : ℝ // x ∈ Set.Icc a b} → ℝ := fun x => f x.val

  have hCont_fRes : Cont fRes := by
    intro U openU
    rcases hf U openU with ⟨V, openV, hEq⟩
    refine ⟨V, openV, ?_⟩
    ext x
    constructor
    · intro hxU
      have hxI : x.val ∈ Set.Icc a b := x.property
      have hxL : x.val ∈ Set.Icc a b ∩ f ⁻¹' U := ⟨hxI, hxU⟩
      have hxR : x.val ∈ Set.Icc a b ∩ V := by
        rw [hEq] at hxL
        exact hxL
      exact hxR.2
    · intro hxV
      have hxI : x.val ∈ Set.Icc a b := x.property
      have hxR : x.val ∈ Set.Icc a b ∩ V := ⟨hxI, hxV⟩
      have hxL : x.val ∈ Set.Icc a b ∩ f ⁻¹' U := by
        rw [hEq.symm] at hxR
        exact hxR
      exact hxL.2

  -- The image f '' [a,b] is connected via a continuous surjection.
  let g : {x : ℝ // x ∈ Set.Icc a b} → {t : ℝ // t ∈ f '' Set.Icc a b} :=
    fun x => ⟨f x.val, ⟨x.val, x.property, rfl⟩⟩

  have hSurj_g : Function.Surjective g := by
    rintro ⟨t, ht⟩
    rcases ht with ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    ext
    rfl

  have hCont_g : Cont g := by
    intro W openW
    rcases openW with ⟨V, openV, rfl⟩
    have hOpen_pre : Open (fRes ⁻¹' V) := hCont_fRes V openV
    have hpre : g ⁻¹' (Subtype.val ⁻¹' V) = fRes ⁻¹' V := by ext x; rfl
    rw [← hpre] at hOpen_pre
    exact hOpen_pre

  have hConn_img : Connected {t : ℝ // t ∈ f '' Set.Icc a b} :=
    (Connected_image g hSurj_g hCont_g) hConn_domain

  -- Connected subsets of ℝ are intervals.
  -- So f '' [a,b] contains everything between f(a) and f(b).
  have hInterval_img : Interval (f '' Set.Icc a b) :=
    (connected_real_subset_iff_interval (A := f '' Set.Icc a b)).1 hConn_img

  have ha_img : f a ∈ f '' Set.Icc a b := by
    refine ⟨a, ?_, rfl⟩
    exact ⟨le_rfl, hab⟩

  have hb_img : f b ∈ f '' Set.Icc a b := by
    refine ⟨b, ?_, rfl⟩
    exact ⟨hab, le_rfl⟩

  have hy_img : y ∈ f '' Set.Icc a b :=
    hInterval_img ha_img hb_img hy.1 hy.2

  rcases hy_img with ⟨c, hc, hfc⟩
  exact ⟨c, hc, hfc⟩
