import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q287 / real_analysis_22):
    Existe una función f : [0, 1] → ℝ que es una contracción débil estricta
    pero no posee un punto fijo en [0, 1]. -/
theorem real_analysis_22 :
    ∃ (f : Set.Icc (0 : ℝ) 1 → ℝ),
      (∀ u v : Set.Icc (0 : ℝ) 1, u ≠ v → ‖f u - f v‖ < ‖(u : ℝ) - v‖) ∧
      (∀ x : Set.Icc (0 : ℝ) 1, f x ≠ (x : ℝ)) := by
  use fun _ => 2
  constructor
  · intro u v huv
    have h_sub_ne : (u : ℝ) - (v : ℝ) ≠ 0 := by
      intro h
      have : (u : ℝ) = (v : ℝ) := sub_eq_zero.mp h
      exact huv (Subtype.ext this)
    have h_norm_pos : 0 < ‖(u : ℝ) - (v : ℝ)‖ := norm_pos_iff.mpr h_sub_ne
    simp only [sub_self, norm_zero]
    exact h_norm_pos
  · intro x hx
    have hx_le : (x : ℝ) ≤ 1 := x.2.2
    linarith
