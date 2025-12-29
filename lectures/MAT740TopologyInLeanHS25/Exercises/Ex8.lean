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
  rcases hx with ⟨m, hmge, rfl⟩
  constructor
  · apply hn
    use m
    constructor
    · exact Nat.le_trans (Nat.le_max_left nA nB) hmge
    · rfl
  · apply hm
    use m
    constructor
    · exact Nat.le_trans (Nat.le_max_right nA nB) hmge
    · rfl


def eventuality' (s : ℕ → X) : MyFilter.Filter X where
  Sets := {A | ∃ n, tail s n ⊆ A}
  /- exercise -/
  univ_Sets := by
    use 0
    intro x hx
    trivial
  upward_Sets := by
    intro A B hA hAB
    obtain ⟨n, hn⟩ := hA
    use n
    apply Set.Subset.trans hn hAB
  inter_Sets := by
    intro A B hA hB
    obtain ⟨nA, hnA⟩ := hA
    obtain ⟨nB, hnB⟩ := hB
    use max nA nB
    apply max_tail' hnA hnB

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
        have F_lim : F lim x := by
          intro N hN
          use N
          exact ⟨hN, Set.Subset.rfl⟩
        have H := h F x F_lim
        have nbhd_fx : Nbhd U (f x) := ⟨open_U, hx⟩
        exact H nbhd_fx
      choose V g using g
      have union_fU : f ⁻¹' U = ⋃₀ {B | ∃ (x : X) (w : x ∈ f ⁻¹' U), B = V x w} := by
        ext z
        constructor
        · intro hz
          have gz := g z hz
          use (V z hz)
          constructor
          · exact ⟨z, hz, rfl⟩
          · exact (gz.1).2
        · intro hz
          obtain ⟨B, ⟨x, wx, rfl⟩, hzB⟩ := hz
          have gx := g x wx
          exact (gx.2) hzB
      rw [union_fU]
      apply Open_sUnion
      intro W hW
      obtain ⟨x,wx,hx⟩ := hW
      specialize g x wx
      rw [hx]
      exact g.1.1

end Ex2
