import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} (f : X → Y) (g : Y → X)

lemma l1 (inv_fg : InverseFun f g) (x : X) : g (f x) = x := by
  sorry

lemma l2 (inv_fg : InverseFun f g) (y : Y) : f (g y) = y := by
  sorry

lemma image_eq_preimage_InverseFun (inv_fg : InverseFun f g) (U : Set X) : f '' U = g ⁻¹' U := by
  sorry

variable [Topology X] [Topology Y]

example : HomeoMap f → OpenMap f := by
  sorry

example (inv_fg : InverseFun f g) (cont_f : Cont f) : OpenMap f → HomeoMap f := by
  sorry

example (bij_f : Function.Bijective f) : OpenMap f ↔ ClosedMap f := by
  sorry
