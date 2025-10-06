import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} [Topology X] [Topology Y]

theorem Cont_preimage_Closed_iff (f : X → Y) : Cont f ↔ (∀ s, Closed s → Closed (f ⁻¹' s)) := by
  sorry
