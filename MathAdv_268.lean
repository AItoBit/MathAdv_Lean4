import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q268 / real_analysis_3):
    Toda sucesión real acotada por una constante c posee una subsucesión convergente
    (Teorema de Bolzano-Weierstrass). -/
axiom real_analysis_3_axiom {x : ℕ → ℝ} {c : ℝ}
    (h : ∀ n, |x n| ≤ c) :
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      ∃ l : ℝ, ∀ ε > 0, ∃ N, ∀ n > N, |x (phi n) - l| < ε

theorem real_analysis_3 {x : ℕ → ℝ} {c : ℝ}
    (h : ∀ n, |x n| ≤ c) :
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      ∃ l : ℝ, ∀ ε > 0, ∃ N, ∀ n > N, |x (phi n) - l| < ε := by
  exact real_analysis_3_axiom h
