import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} [Topology X] [Topology Y]

theorem Cont_preimage_Closed_iff (f : X → Y) : Cont f ↔ (∀ s, Closed s → Closed (f ⁻¹' s)) := by
  constructor
  case mp =>
    intro cont_f C closed_C
    rw [Closed] at closed_C
    apply cont_f at closed_C
    exact closed_C
  case mpr =>
    intro h U open_U
    have w : Closed (Uᶜ) := by
      rw [Closed, compl_compl]
      exact open_U
    specialize h Uᶜ w
    rw [Closed, Set.preimage_compl, compl_compl] at h
    exact h
