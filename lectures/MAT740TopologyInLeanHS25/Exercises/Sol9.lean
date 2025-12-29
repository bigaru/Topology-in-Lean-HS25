import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.Connectedness

open MyConnected

variable {X Y : Type*} [Topology X] [Topology Y]

theorem Disconnected_Prop : ¬(Connected Prop) := by
  rw [Connected]
  push_neg
  have cont_id : Cont (id : Prop → Prop) := Cont_id
  have non_const : ∀ b : Prop, ¬(Constant id b) := by
    intro b
    rw [Constant]
    push_neg
    have w : b = True ∨ b = False := by
        exact Classical.propComplete b
    obtain c1|c2 := w
    case inl =>
      use False
      rw [c1]
      simp only [id_eq, ne_eq, eq_iff_iff, iff_true, not_false_eq_true]
    case inr =>
      use True
      rw [c2]
      simp only [id_eq, ne_eq, eq_iff_iff, iff_false, not_true_eq_false, not_false_eq_true]
  use id

theorem Connected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : Connected X → Connected Y := by
    intro connected_X k cont_k
    specialize connected_X (k ∘ f) (Cont_comp f k cont_f cont_k)
    obtain ⟨b, constant_kf⟩ := connected_X
    use b
    intro y
    specialize surj_f y
    obtain ⟨a,ha⟩ := surj_f
    rw [← ha]
    exact constant_kf a

theorem PathConnected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : PathConnected X → PathConnected Y := by
    intro pathconnected_X u v
    obtain ⟨x, hx⟩ := surj_f u
    obtain ⟨y, hy⟩ := surj_f v
    have pathX : Path x y := Classical.choice (pathconnected_X x y)
    have pathY : Path (f x) (f y) := mapPath f cont_f pathX
    rw [hx,hy] at pathY
    constructor
    exact pathY
