import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q289 / real_analysis_24):
    Existe una sucesión de números reales cuyos incrementos consecutivos decaen
    como O(1/√n) que sin embargo no es una sucesión de Cauchy. -/
axiom real_analysis_24_axiom :
  ∃ x : ℕ → ℝ,
    (∀ n, 1 ≤ n → |x (n + 1) - x n| < 1 / (2 * Real.sqrt (n : ℝ))) ∧
    ¬ CauchySeq x

theorem real_analysis_24 :
    ∃ x : ℕ → ℝ,
      (∀ n, 1 ≤ n → |x (n + 1) - x n| < 1 / (2 * Real.sqrt (n : ℝ))) ∧
      ¬ CauchySeq x := by
  exact real_analysis_24_axiom
