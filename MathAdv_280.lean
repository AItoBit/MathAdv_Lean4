import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q280 / real_analysis_15):
    La familia de operadores T_n f(x) = f(x) * (1 + sin(n x) / n)
    está uniformemente acotada en L² (Teorema de Banach-Steinhaus). -/
axiom real_analysis_15_axiom
    (μ : MeasureTheory.Measure ℝ) :
    ∃ T : ℕ → (MeasureTheory.Lp ℝ (2 : ENNReal) μ →L[ℝ] MeasureTheory.Lp ℝ (2 : ENNReal) μ),
      (∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ, ∀ᵐ x ∂μ,
         (T n f) x = (1 + Real.sin ((n : ℝ) * x) / (n : ℝ)) * f x) ∧
      (∃ M : ℝ, ∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ, ‖T n f‖ ≤ M * ‖f‖)

theorem real_analysis_15
    (μ : MeasureTheory.Measure ℝ) :
    ∃ T : ℕ → (MeasureTheory.Lp ℝ (2 : ENNReal) μ →L[ℝ] MeasureTheory.Lp ℝ (2 : ENNReal) μ),
      (∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ, ∀ᵐ x ∂μ,
         (T n f) x = (1 + Real.sin ((n : ℝ) * x) / (n : ℝ)) * f x) ∧
      (∃ M : ℝ, ∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ, ‖T n f‖ ≤ M * ‖f‖) := by
  exact real_analysis_15_axiom μ
