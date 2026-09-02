import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q266 / real_analysis_1):
    Toda función diferenciable en ℝ cuya derivada es idénticamente cero
    es constante. -/
theorem real_analysis_1 {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (h : ∀ x, deriv f x = 0) :
    ∃ c : ℝ, ∀ x, f x = c := by
  use f 0
  intro x
  exact is_const_of_deriv_eq_zero hf h x 0
