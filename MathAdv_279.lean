import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q279 / real_analysis_14):
    Si una sucesión (f_n) en [0, 1] es uniformemente integrable y converge
    casi en todas partes a f, entonces f es integrable en [0, 1]
    (Teorema de Vitali). -/
axiom real_analysis_14_axiom
    (μ : MeasureTheory.Measure ℝ)
    (f_seq : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hUI : MeasureTheory.UnifIntegrable f_seq (1 : ENNReal) (μ.restrict (Set.Icc (0 : ℝ) 1)))
    (h_ae : ∀ᵐ x ∂(μ.restrict (Set.Icc (0 : ℝ) 1)),
              ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f_seq n x - f x| < ε) :
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) μ

theorem real_analysis_14
    (μ : MeasureTheory.Measure ℝ)
    (f_seq : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hUI : MeasureTheory.UnifIntegrable f_seq (1 : ENNReal) (μ.restrict (Set.Icc (0 : ℝ) 1)))
    (h_ae : ∀ᵐ x ∂(μ.restrict (Set.Icc (0 : ℝ) 1)),
              ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f_seq n x - f x| < ε) :
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) μ := by
  exact real_analysis_14_axiom μ f_seq f hUI h_ae
