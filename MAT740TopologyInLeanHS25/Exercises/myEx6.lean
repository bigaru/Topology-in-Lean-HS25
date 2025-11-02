import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.NewSpaces

universe u
variable {X : Type u} [TX : Topology X]

open Constructions

instance Subspace_pullbackTopology' {S : Type u} (incl : S → X) (inj : Function.Injective incl)
  : Subspace X where
    S := S
    TS := pullbackTopology X TX S incl
    incl := incl
    Injective_incl := inj
    char_Subspace := by
      intro T TT f
      constructor
      · intro h
        intro U open_U
        simp only [Cont] at h

        specialize h (incl ⁻¹' U) (⟨U, open_U, rfl⟩)
        rw [Set.preimage_comp]
        exact h

      · intro h
        simp only [Cont] at h
        simp only [Cont]
        intro U open_U

        rcases open_U with ⟨W, open_W, rfl⟩
        specialize h W open_W
        rw [← Set.preimage_comp]
        exact h


theorem Cont_qmap' [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
    let h := quot.char_Quotient (TT := quot.TQ) (f := id)
    exact (h.mp (@Cont_id quot.Q quot.TQ))


/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient' [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
    intro h
    let hchar := quot.char_Quotient (TT := TQ') (f := id)
    exact hchar.mpr h


instance pushforwardTopology'
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      rw [Set.preimage_univ]
      exact Open_univ

    Open_inter := by
      intro U V open_U open_V
      rw [Set.preimage_inter]
      exact Open_inter open_U open_V

    Open_sUnion := by
      intro C hC
      rw [Set.preimage_sUnion, ← Set.sUnion_image]
      apply Open_sUnion

      intro t ht
      rw [Set.mem_image] at ht
      obtain ⟨U, hU1, rfl⟩ := ht
      exact hC U hU1


instance Quotient_pushforwardTopology'
  {Q : Type u} (qmap : X → Q) (surj : Function.Surjective qmap)
  : Quotient X where
    Q := Q
    TQ := pushforwardTopology X TX Q qmap
    qmap := qmap
    Surjective_qmap := surj
    char_Quotient := by
      intro T TT f
      constructor
      · intro cont_f
        intro U open_U
        specialize cont_f U open_U
        rw [Set.preimage_comp]
        exact cont_f

      · intro cont_fq
        intro U open_U
        specialize cont_fq U open_U
        rw [Set.preimage_comp] at cont_fq
        exact cont_fq
