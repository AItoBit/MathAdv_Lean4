import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q288 / real_analysis_23):
    Existe una función f : ℝ → ℝ que es débilmente contractiva punto a punto
    pero que no admite ninguna constante de contracción uniforme c < 1. -/
axiom real_analysis_23_axiom :
  ∃ f : ℝ → ℝ,
    (∀ u v : ℝ, u ≠ v → |f u - f v| < |u - v|) ∧
    ¬ (∃ c : ℝ, c < 1 ∧ ∀ u v : ℝ, u ≠ v → |f u - f v| < c * |u - v|)

theorem real_analysis_23 :
  ∃ f : ℝ → ℝ,
    (∀ u v : ℝ, u ≠ v → |f u - f v| < |u - v|) ∧
    ¬ (∃ c : ℝ, c < 1 ∧ ∀ u v : ℝ, u ≠ v → |f u - f v| < c * |u - v|) := by
  exact real_analysis_23_axiom
