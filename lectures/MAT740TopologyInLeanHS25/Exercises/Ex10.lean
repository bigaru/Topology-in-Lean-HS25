import Mathlib.Tactic

import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u

structure openCover (I : Type u) (X : Type u) [Topology X] where
  Cover : I → Set X
  Open_cover : ∀ i, Open (Cover i)
  Is_cover : (⋃ i, Cover i) = Set.univ

def subCover {I J : Type u} {X : Type u} [Topology X] (s : I → J) (C : openCover J X) : Prop :=
  Function.Injective s ∧
  (⋃ i : I, C.Cover (s i)) = Set.univ

def Compact (X : Type u) [Topology X] : Prop
  := ∀ (I : Type u) (C : openCover I X), ∃ (N : Type u) (s : N → I), Finite N ∧ subCover s C

variable {X Y : Type u} [Topology X] [Topology Y]

def pullbackCover {I : Type u} (f : X → Y) (cont_f : Cont f) (C : openCover I Y)
  : openCover I X where
  Cover := fun i ↦ f ⁻¹' (C.Cover i)
  Open_cover := by
    sorry
  Is_cover := by
    sorry

theorem Compact_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f) :
  Compact X → Compact Y := by
  sorry
