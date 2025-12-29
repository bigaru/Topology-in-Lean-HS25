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
      sorry -- exercise

theorem Cont_qmap' [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
  sorry -- exercise

/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient' [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
    sorry -- exercise

instance pushforwardTopology'
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      sorry
    Open_inter := by
      sorry
    Open_sUnion := by
      sorry -- hint : Open_preimageUnion

instance Quotient_pushforwardTopology'
  {Q : Type u} (qmap : X → Q) (surj : Function.Surjective qmap)
  : Quotient X where
    Q := Q
    TQ := pushforwardTopology X TX Q qmap
    qmap := qmap
    Surjective_qmap := surj
    char_Quotient := by
      sorry --exercise
