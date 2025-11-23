import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.Connectedness

open MyConnected

variable {X Y : Type*} [Topology X] [Topology Y]

theorem Disconnected_Prop : ¬(Connected Prop) := by
  rw [Connected]
  push_neg
  have cont_id : Cont (id : Prop → Prop) := Cont_id
  have non_const : ∀ b : Prop, ¬(Constant id b) := by
    intro b hb
    have eqF : False = b := by
      simpa [id] using hb False
    have eqT : True = b := by
      simpa [id] using hb True
    let e := eqF.trans eqT.symm
    contradiction
  use id

theorem Connected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
: Connected X → Connected Y := by
    intro hX hY cont_hY
    have cont_hYf : Cont (hY ∘ f) := Cont_comp f hY cont_f cont_hY
    obtain ⟨b, const_hYf⟩ := hX (hY ∘ f) cont_hYf
    use b
    intro y
    obtain ⟨x, hx⟩ := surj_f y
    have hfinal : hY (f x) = b := const_hYf x
    rw [hx] at hfinal
    exact hfinal


theorem PathConnected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : PathConnected X → PathConnected Y := by
    intro hP y1 y2
    obtain ⟨x1, hx1⟩ := surj_f y1
    obtain ⟨x2, hx2⟩ := surj_f y2
    have np : Nonempty (Path x1 x2) := hP x1 x2
    let p := Classical.choice np
    let mp := mapPath f cont_f p
    let pathY : Path y1 y2 :=
      { p := mp.p
        Cont_p := mp.Cont_p
        source := mp.source.trans hx1
        target := mp.target.trans hx2 }
    exact ⟨pathY⟩
