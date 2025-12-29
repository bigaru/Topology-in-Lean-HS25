import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.NewSpaces

section Ex1
variable (I : Type) (J : I → Type) (P : (i : I) → J i → Prop)

theorem dist_quant : (∀ i, ∃ j : J i, P i j) ↔ (∃ c : (i : I) → J i, ∀ i, P i (c i)) := by
  constructor
  case mp =>
    intro h
    choose c hc using h
    use c
  case mpr =>
    intro h i
    obtain ⟨c, hc⟩ := h
    use (c i)
    apply hc

end Ex1

section Ex2
universe u
open Constructions

instance Coproduct_coproductTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y]
  : CoproductSpace X Y where
  TC := coproductTopology X Y
  char_Coproduct := by
    intro T TT f
    constructor
    case mp =>
      intro cont_f
      have h : ∀ U : Set T, Open U → Open (f ∘ Sum.inl ⁻¹' U) ∧ Open (f ∘ Sum.inr ⁻¹' U) := by
        intro U open_U
        apply cont_f U open_U
      constructor
      case left =>
        intro U open_U
        exact (h U open_U).left
      case right =>
        intro U open_U
        exact (h U open_U).right
    case mpr =>
      intro h U open_U
      have h1 := h.left U open_U
      have h2 := h.right U open_U
      exact ⟨h1, h2⟩
end Ex2

section Bonus
variable (I : Type*) (J : I → Type*) (X : (i : I) → J i → Type*)

instance dist_type : (Π i, Σ j : J i, X i j) ≃ (Σ c : (i : I) → J i, Π i, X i (c i)) where
  toFun :=
    fun h ↦
      let c : (i : I) → J i :=
        fun i ↦ (h i).1
      ⟨c, fun i ↦ (h i).2⟩
  invFun :=
    fun h i =>
      let c := h.1
      ⟨c i, h.2 i⟩

end Bonus
