import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces

open Set

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w} [Topology X] [Topology Y] [Topology Z]

/- # Continuous Functions -/

/- A function `f : X → Y` is continuous iff preimages of open sets are open. -/
@[simp]
def Cont (f : X → Y) : Prop := ∀ s, Open s → Open (f ⁻¹' s)

/- Constant maps are continuous. -/
-- Next time

/- Identity maps are continuous. -/
@[simp]
theorem Cont_id : Cont (id : X → X) := by
  intro U open_U
  rw [preimage_id]
  exact open_U

/- Compositions of continuous functions are continuous -/
@[simp]
theorem Cont_comp (f : X → Y) (g : Y → Z) (cf : Cont f) (cg : Cont g) : Cont (g ∘ f) := by
  intro U open_U
  specialize cg U open_U
  specialize cf (g ⁻¹' U) cg
  exact cf
