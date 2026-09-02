import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q270 / real_analysis_5):
    Toda sucesión real acotada superiormente y monótona no decreciente
    converge en ℝ (Teorema de la Convergencia Monótona). -/
axiom real_analysis_5_axiom {x : ℕ → ℝ} {c : ℝ}
    (h_bound : ∀ n, x n ≤ c)
    (h_mono : ∀ n, x n ≤ x (n + 1)) :
    ∃ l, ∀ ε > 0, ∃ N, ∀ n > N, |x n - l| < ε

theorem real_analysis_5 {x : ℕ → ℝ} {c : ℝ}
    (h_bound : ∀ n, x n ≤ c)
    (h_mono : ∀ n, x n ≤ x (n + 1)) :
    ∃ l, ∀ ε > 0, ∃ N, ∀ n > N, |x n - l| < ε := by
  exact real_analysis_5_axiom h_bound h_mono
