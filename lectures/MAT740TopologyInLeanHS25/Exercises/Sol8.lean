import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters

open MyFilter

variable {X Y : Type*} {A B : Set X}

section Ex1

lemma max_tail' {s : ℕ → X} {nA nB : ℕ}
(hn : tail s nA ⊆ A) (hm : tail s nB ⊆ B)
: tail s (max nA nB) ⊆ A ∩ B := by
  intro x hx
  obtain ⟨m, hm1, hm2⟩ := hx
  have w1 : m ≥ nA := by
    exact le_of_max_le_left hm1
  have w2 : m ≥ nB := by
    exact le_of_max_le_right hm1
  have xA : x ∈ A := by
    apply hn
    use m
  have xB : x ∈ B := by
    apply hm
    use m
  exact ⟨xA,xB⟩

def eventuality' (s : ℕ → X) : MyFilter.Filter X where
  Sets := {A | ∃ n, tail s n ⊆ A}
  /- exercise -/
  univ_Sets := by use 0; apply Set.subset_univ
  upward_Sets := by
    intro A B hA A_sub_B
    obtain ⟨nA,hnA⟩ := hA
    use nA
    exact Set.Subset.trans hnA A_sub_B
  inter_Sets := by
    intro A B hA hB
    obtain ⟨nA,hnA⟩ := hA
    obtain ⟨nB,hnB⟩ := hB
    use (max nA nB)
    apply max_tail hnA hnB

end Ex1

section Ex2

theorem Cont_convergence' [Topology X] [Topology X] (f : X → Y)
  : Cont f ↔ ∀ (G : MyFilter.Filter X) (x : X), G lim x → (mapFilter f G) lim (f x) := by
    constructor
    case mp => sorry -- no need to fill this in
    case mpr =>
      intro h U open_U
      have g : ∀ x ∈ f ⁻¹' U, ∃ V, Nbhd V x ∧ V ⊆ f ⁻¹' U := by
        intro x hx
        let F := NbhdFilter x
        have F_lim_x : F lim x := by
          intro U hU
          have w1 : Nbhd U x := by
            exact hU
          have w2 : U ⊆ U := by
            trivial
          use U
        specialize h F x F_lim_x
        have w : f ⁻¹' U ∈ F := by
          apply h
          exact ⟨open_U, hx⟩
        obtain ⟨V,hV1,hV2⟩ := w
        use V
      choose V g using g
      have union_fU : f ⁻¹' U = ⋃₀ {B | ∃ (x : X) (w : x ∈ f ⁻¹' U), B = V x w} := by
        ext x
        constructor
        case mp =>
          intro wx
          use V x wx
          constructor
          case left => use x; use wx
          case right => specialize g x wx; exact g.1.2
        case mpr =>
          intro hx
          obtain ⟨B,hB1,hB2⟩ := hx
          obtain ⟨y,wy,hy⟩ := hB1
          specialize g y wy
          apply g.2
          rw [← hy]
          exact hB2
      rw [union_fU]
      apply Open_sUnion
      intro W hW
      obtain ⟨x,wx,hx⟩ := hW
      specialize g x wx
      rw [hx]
      exact g.1.1

end Ex2
