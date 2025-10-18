import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} (f : X → Y) (g : Y → X)

lemma l1 (inv_fg : InverseFun f g) (x : X) : g (f x) = x := by
  rw [InverseFun] at inv_fg
  obtain ⟨h1, h2⟩ := inv_fg

  rw [funext_iff] at h2
  simp only [Function.comp_apply, id_eq] at h2
  exact h2 x

lemma l2 (inv_fg : InverseFun f g) (y : Y) : f (g y) = y := by
  rw [InverseFun] at inv_fg
  obtain ⟨h1, h2⟩ := inv_fg

  rw [funext_iff] at h1
  simp only [Function.comp_apply, id_eq] at h1
  exact h1 y

lemma image_eq_preimage_InverseFun (inv_fg : InverseFun f g) (U : Set X) : f '' U = g ⁻¹' U := by
  ext y
  constructor
  · intro hf
    rcases hf with ⟨x, hxU, rfl⟩
    rw [Set.mem_preimage]
    rw [l1 f g inv_fg x]
    exact hxU

  · intro hg
    use g y
    rw [l2 f g inv_fg y]
    constructor
    · rw [Set.mem_preimage] at hg
      exact hg
    · rfl

variable [Topology X] [Topology Y]

example : HomeoMap f → OpenMap f := by
  intro h
  rcases h.2 with ⟨g, gCont, inv_fg⟩
  intro U hU
  rw [image_eq_preimage_InverseFun f g inv_fg U]
  apply gCont
  exact hU

example (inv_fg : InverseFun f g) (cont_f : Cont f) : OpenMap f → HomeoMap f := by
  intro h
  constructor
  · exact cont_f
  · use g
    constructor
    · rw [Cont]
      intro U hU
      rw [← image_eq_preimage_InverseFun f g inv_fg U]
      exact h U hU
    · exact inv_fg

/-
  Bonus
 -/
example (bij_f : Function.Bijective f) : OpenMap f ↔ ClosedMap f := by
  sorry
