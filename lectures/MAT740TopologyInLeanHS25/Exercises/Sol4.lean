import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.ContinuousFunctions

universe u v
variable {X : Type u} {Y : Type v} (f : X → Y) (g : Y → X)

lemma l1 (inv_fg : InverseFun f g) (x : X) : g (f x) = x := by
  obtain ⟨h1,h2⟩ := inv_fg
  rw [funext_iff] at h2
  apply h2

lemma l2 (inv_fg : InverseFun f g) (y : Y) : f (g y) = y := by
  obtain ⟨h1,h2⟩ := inv_fg
  rw [funext_iff] at h1
  apply h1

lemma image_eq_preimage_InverseFun (inv_fg : InverseFun f g) (U : Set X) : f '' U = g ⁻¹' U := by
  ext y; constructor
  case mp =>
    intro hy
    obtain ⟨x, hx1, hx2⟩ := hy
    rw [Set.mem_preimage, ← hx2, l1 f g inv_fg x]
    exact hx1
  case mpr =>
    intro hy
    use g y
    constructor
    case left => exact hy
    case right => exact l2 f g inv_fg y

variable [Topology X] [Topology Y]

example : HomeoMap f → OpenMap f := by
  intro homeo_f U open_U
  obtain ⟨cont_f, ⟨g2, cont_g2, inv_fg2⟩ ⟩ := homeo_f
  rw [image_eq_preimage_InverseFun f g2 inv_fg2 U]
  apply cont_g2
  exact open_U

example (inv_fg : InverseFun f g) (cont_f : Cont f) : OpenMap f → HomeoMap f := by
  intro open_f
  constructor
  case left => exact cont_f
  case right =>
    use g
    constructor
    case left =>
      intro U open_U
      rw [← image_eq_preimage_InverseFun f g inv_fg U]
      apply open_f
      exact open_U
    case right => exact inv_fg

example (bij_f : Function.Bijective f) : OpenMap f ↔ ClosedMap f := by
  constructor
  case mp =>
    intro open_f C closed_C
    have open_Cc : Open Cᶜ := by
      apply closed_C
    apply open_f at open_Cc
    rw [Closed]
    rw [← Set.image_compl_eq bij_f]
    exact open_Cc
  case mpr =>
    intro closed_f U open_U
    have closed_Uc : Closed Uᶜ := by
      simp only [Closed, compl_compl]
      exact open_U
    apply closed_f at closed_Uc
    rw [Set.image_compl_eq bij_f] at closed_Uc
    simp only [Closed, compl_compl] at closed_Uc
    exact closed_Uc
