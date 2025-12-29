import Mathlib.Tactic

open Set

universe u v

/- A topology on a type `X`. -/
class Topology (X : Type u) : Type u where
  /- A predicate witnessing that a set `s : Set X` is open. -/
  Open : Set X → Prop
  /- The universal `{x : X | True}` is open. -/
  Open_univ : Open univ
  /- Binary intersection of open sets are open. -/
  Open_inter : ∀ s t, Open s → Open t → Open (s ∩ t)
  /- Unions of families of open sets are open. -/
  Open_sUnion : ∀ s, (∀ t ∈ s, Open t) → Open (⋃₀ s)

/- # Open and Closed sets -/

variable {X : Type u} {Y : Type v} [Topology X] [Topology Y] {s t : Set X}

/- Predicate on subsets of the ambient topology on `X` -/
def Open (s : Set X) : Prop := Topology.Open s

/- A set is closed if its complement is open. -/
@[simp]
def Closed (s : Set X) : Prop := Open (sᶜ)

/- A neighborhood of `x : X` is an open set containing `x` -/
@[simp]
def Nbhd (s : Set X) (x : X) := Open s ∧ x ∈ s

/- We state the defining properties of a topology as theorems to easily apply them in proofs. -/
@[simp]
theorem Open_univ : Open (univ : Set X) := Topology.Open_univ

@[simp]
theorem Open_inter (hs : Open s) (ht : Open t) : Open (s ∩ t) := Topology.Open_inter s t hs ht

@[simp]
theorem Open_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, Open t) : Open (⋃₀ s) := Topology.Open_sUnion s h

@[simp]
theorem Open_empty : Open (∅ : Set X) := by
  have w : ∀ t ∈ (∅ : Set (Set X)), Open t := by
    intro t ht; contradiction
  apply Open_sUnion at w
  rw [sUnion_empty] at w
  exact w

/- # Instances of topologies. -/

/- For every type `X`, there is a topology on `X` where every subset is open. -/
instance discreteTopology (X : Type u) : Topology X where
  Open := fun x => True
  Open_univ := by trivial
  Open_inter := by intros; trivial
  Open_sUnion := by intros; trivial
