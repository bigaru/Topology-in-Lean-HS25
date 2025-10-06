import Mathlib.Tactic

open Set

universe u v

/- A topology on a type `X` -/
class Topology (X : Type u) : Type u where
  /- A predicate witnessing that a set `s : Set X` is open. -/
  Open : Set X → Prop
  /- The universal set {x : X | True} is open. -/
  Open_univ : Open Set.univ
  /- Binary intersections of opens are open. -/
  Open_inter : ∀ s t, Open s → Open t → Open (s ∩ t)
  /- Unions of families of open sets are open. -/
  Open_sUnion : ∀ s, (∀ t ∈ s, Open t) → Open (⋃₀ s)

/- # Open and Closed sets -/

variable {X : Type u} {Y : Type v} [Topology X] [Topology Y] {s t : Set X}

/- Predicate on subsets of ambient topology on X. -/
def Open (s : Set X) : Prop := Topology.Open s

/- A set is closed if its complement is open. -/
@[simp]
def Closed (s : Set X) : Prop := Open sᶜ

@[simp]
/- A neighborhood of `x : X` is an open set containing `x`. -/
def Nbhd (s : Set X) (x : X) := Open s ∧ x ∈ s

/- We state the defining properties as theorems so we can apply them easily in proofs. -/
@[simp]
theorem Open_univ : Open (univ : Set X) := Topology.Open_univ

@[simp]
theorem Open_inter (hs : Open s) (ht : Open t) : Open (s ∩ t) := Topology.Open_inter s t hs ht

@[simp]
theorem Open_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, Open t) : Open (⋃₀ s) :=
  Topology.Open_sUnion s h

@[simp]
theorem Open_empty : Open (∅ : Set X) := by
  have w : ∀ t ∈ (∅ : Set (Set X)), Open t := by
    intro t ht
    contradiction
  apply Open_sUnion at w
  rw [sUnion_empty] at w
  exact w

/- # Instances of topologies -/

/- For every type `X`, there is a topology on `X` where every set is open. -/
instance discreteTopology (X : Type u) : Topology X where
  Open := fun s => True
  Open_univ := by trivial
  Open_inter := by intros ; trivial
  Open_sUnion := by intros ; trivial

/- For every type `X`, there is a topology on `X` where only `∅` and `univ` are open. -/
instance indiscreteTopology (X : Type u) : Topology X where
  Open := fun s => s = ∅ ∨ s = univ
  Open_univ := by right ; rfl
  Open_inter := by
    intro a b ha hb
    obtain ha1 | ha2 := ha
    case inl =>
      left ; rw [ha1] ; simp
    case inr =>
      obtain hb1 | hb2 := hb
      case inl =>
        left ; rw [hb1] ; simp
      case inr =>
        right ; rw [ha2, hb2]; simp
  Open_sUnion := by
    intro s hs
    by_cases c : univ ∈ s
    case pos =>
      right
      rw [sUnion_eq_univ_iff]
      intro x
      use univ
      exact ⟨c, trivial⟩
    case neg =>
      left
      rw [sUnion_eq_empty]
      intro t ht
      specialize hs t ht
      obtain hs1 | hs2 := hs
      case inl => exact hs1
      case inr => rw [hs2] at ht; contradiction

instance restrictionTopology [Topology X] (U : Set X) (open_U : Open U) : Topology ↥U where
  Open := fun s => Open (U ∩ s)
  Open_univ := by
    rw [Subtype.coe_image_univ, inter_eq_self_of_subset_left fun {a} a => a]
    exact open_U
  Open_inter := by
    sorry
  Open_sUnion := by sorry
