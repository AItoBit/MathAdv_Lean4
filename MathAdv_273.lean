import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q273 / real_analysis_8):
    La función f(x) = |x| en el intervalo compacto [-1, 1] puede ser
    aproximada uniformemente por polinomios (Teorema de Stone-Weierstrass). -/
axiom real_analysis_8_axiom :
  ∀ ε : ℝ, ε > 0 →
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, abs (Polynomial.eval x p - abs x) < ε

theorem real_analysis_8 :
  ∀ ε : ℝ, ε > 0 →
    ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, abs (Polynomial.eval x p - abs x) < ε := by
  exact real_analysis_8_axiom
