import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.Connectedness

open MyConnected

variable {X : Type*} [Topology X]

structure Loop (x : X) where
  loop : I → X
  Cont_loop : Cont loop
  source_eq_x : loop zero = x
  target_eq_x : loop one = x

def Loop' (x : X) := Path x x

structure homotopy {x : X} (l1 l2 : Loop x) where
  H : I × I → X
  Cont_H : Cont H
  fixed_source : ∀ t, H ⟨t,zero⟩ = x
  fixed_target : ∀ t, H ⟨t,one⟩ = x

def Homotopic {x : X} (l1 l2 : Loop x) : Prop := Nonempty (homotopy l1 l2)

lemma Homotopic_refl {x : X} (l : Loop x) : Homotopic l l := by
  sorry

lemma Homotopic_symm {x : X} (l1 l2 : Loop x) :
  Homotopic l1 l2 → Homotopic l2 l1 := by
  sorry

lemma Homotopic_trans {x : X} (l1 l2 l3 : Loop x) :
  Homotopic l1 l2 → Homotopic l2 l3 → Homotopic l1 l3 := by
  sorry

instance LoopSetoid (x : X) : Setoid (Loop x) where
  r := Homotopic
  iseqv := by
    constructor
    case refl => exact Homotopic_refl
    case symm => intro l1 l2; exact Homotopic_symm l1 l2
    case trans => intro l1 l2 l3; exact Homotopic_trans l1 l2 l3

@[simp]
theorem LoopEquiv {x : X} (f g : Loop x) : f ≈ g ↔ Homotopic f g := by trivial

def LoopSpace (x : X) := Quotient (LoopSetoid x)

/-
Working with quotients:

Basic defs: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Quotient

More theorems: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#Quotient.eq_iff_equiv
-/

example {x : X} (f g : Loop x) : Quotient.mk (LoopSetoid x) f = Quotient.mk (LoopSetoid x) g := by
  rw [Quotient.eq_iff_equiv, LoopEquiv]
  sorry

def loop_comp {x : X} (l1 l2 : Loop x) : Loop x := by
  constructor
  case loop =>
    intro i
    sorry -- bad definition of I???
    ---exact (if i.val < 1/2 then l1.loop i else l2.loop i)
  case Cont_loop => sorry
  case source_eq_x => sorry
  case target_eq_x => sorry

def loop_unit {x : X} : Loop x := by sorry

def loop_inv {x : X} (l1 : Loop x) : Loop x := by sorry

instance FundamentalGroup (x : X) : Group (LoopSpace x) where
  mul := by
    intro l1 l2
    apply Quotient.mk
    refine Quotient.lift₂ loop_comp ?_ l1 l2
    sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  inv_mul_cancel := sorry

variable (x : X) (f g : LoopSpace x)
#check f⁻¹ * g * 1
