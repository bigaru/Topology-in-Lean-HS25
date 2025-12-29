import Mathlib.Tactic
import ConnectedSpaces.Definitions.Connectedness

open MyConnected

def Interval (A : Set ℝ) : Prop :=
  /- Assuming a ≤ b -/
  ∀ {a b x : ℝ}, a ∈ A → b ∈ A → a ≤ x → x ≤ b → x ∈ A

/- Similarly for others Ioo, Ico, Ioc -/
example : Interval (Set.Icc 0 1) := by
  intro a b x ha hb hax hxb
  repeat rw [Set.mem_Icc] at ha hb
  constructor
  · linarith
  · linarith

theorem real_connected_iff_real_interval (A : Set ℝ) : Connected A ↔ Interval A :=
  by sorry
