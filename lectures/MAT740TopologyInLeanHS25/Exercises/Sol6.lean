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
      case mp =>
        intro cont_f V open_V
        rw [Set.preimage_comp]
        apply cont_f
        use V
      case mpr =>
        intro cont_if U open_U
        obtain ⟨V, hV1, hV2⟩ := open_U
        rw [hV2]
        rw [← Set.preimage_comp]
        apply cont_if
        exact hV1

theorem Cont_qmap' [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
    have h : id ∘ quot.qmap = quot.qmap := by
      exact rfl
    rw [← h]
    rw [← quot.char_Quotient]
    intro U open_U
    exact open_U

/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient' [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
    intro h
    rw [Coarser]
    rw [quot.char_Quotient, Function.id_comp]
    exact h

instance pushforwardTopology'
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      simp only [Set.preimage_univ, Open_univ]
    Open_inter := by
      intro U V hU hV
      rw [Set.preimage_inter]
      exact Open_inter hU hV
    Open_sUnion := by
      intro C hC
      rw [Set.preimage_sUnion]
      exact Open_preimageUnion hC

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
      case mp =>
        intro cont_f U open_U
        apply cont_f
        exact open_U
      case mpr =>
        intro cont_fq U open_U
        exact cont_fq U open_U
