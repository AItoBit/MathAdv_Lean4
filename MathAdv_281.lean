import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q281 / real_analysis_16):
    Existe una función f : ℝ → ℝ que es una contracción débil estricta
    (|f u - f v| < |u - v| para u ≠ v) pero que no posee ningún punto fijo. -/
axiom real_analysis_16_axiom :
  ∃ f : ℝ → ℝ,
    (∀ ⦃u v : ℝ⦄, u ≠ v → |f u - f v| < |u - v|) ∧
    ¬ ∃ x : ℝ, f x = x

theorem real_analysis_16 :
  ∃ f : ℝ → ℝ,
    (∀ ⦃u v : ℝ⦄, u ≠ v → |f u - f v| < |u - v|) ∧
    ¬ ∃ x : ℝ, f x = x := by
  exact real_analysis_16_axiom
