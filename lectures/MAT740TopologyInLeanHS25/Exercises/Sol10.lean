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
    intro i
    apply cont_f
    exact C.Open_cover i
  Is_cover := by
    rw [← Set.preimage_iUnion, C.Is_cover, Set.preimage_univ]

theorem Compact_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f) :
  Compact X → Compact Y := by
  intro compact_X
  intro I C
  let D := pullbackCover f cont_f C
  rw [Compact] at compact_X
  obtain ⟨N,s,fin_N,sub_s_D⟩  := compact_X I D
  use N ; use s
  constructor
  case left => exact fin_N
  case right =>
    constructor
    case left => exact sub_s_D.1
    case right =>
      rw [Set.iUnion_eq_univ_iff]
      intro y
      obtain ⟨x, hx⟩ := surj_f y
      rw [← @Set.mem_iUnion, ← hx, ← Set.mem_preimage, Set.preimage_iUnion]
      have w : x ∈ ⋃ i, D.Cover (s i) := by
        rw [sub_s_D.2]
        trivial
      apply w
