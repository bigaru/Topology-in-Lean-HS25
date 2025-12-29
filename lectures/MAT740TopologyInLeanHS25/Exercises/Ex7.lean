import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.NewSpaces

section Ex1
variable (I : Type) (J : I → Type) (P : (i : I) → J i → Prop)

theorem dist_quant : (∀ i, ∃ j : J i, P i j) ↔ (∃ c : (i : I) → J i, ∀ i, P i (c i)) := by
  -- hint: use the `choose` tactic
  constructor
  · intro h
    choose c hc using h
    exact ⟨c, hc⟩
  · intro h
    rcases h with ⟨c, hc⟩
    intro i
    exact ⟨c i, hc i⟩

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
    · intro h
      constructor
      · intro U open_U
        -- unfold continuity for `f` to specialize it at `U`
        simp only [Cont] at h
        have hf := h U open_U
        rcases hf with ⟨h_inl, h_inr⟩
        exact h_inl

      · intro U open_U
        simp only [Cont] at h
        have hf := h U open_U
        rcases hf with ⟨h_inl, h_inr⟩
        exact h_inr

    · intro h
      rcases h with ⟨hL, hR⟩
      intro U open_U
      exact ⟨hL U open_U, hR U open_U⟩
end Ex2

section Bonus
variable (I : Type*) (J : I → Type*) (X : (i : I) → J i → Type*)

instance dist_type : (Π i, Σ j : J i, X i j) ≃ (Σ c : (i : I) → J i, Π i, X i (c i)) where
  toFun := sorry
  invFun := sorry
  -- the following are not required once toFun and invFun correctly
  left_inv := sorry
  right_inv := sorry

/- Hint: You can either define toFun and invFun
1) using anonymous functions
2) using tactics mode.
If you use anonymous functions, you can type `_` to see the context and what type lean expects.
-/

end Bonus
