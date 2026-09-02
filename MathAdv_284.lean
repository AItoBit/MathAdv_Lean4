import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q284 / real_analysis_19):
    En un espacio métrico completo, toda sucesión de Cauchy converge
    (Definición/caracterización de completitud). -/
theorem real_analysis_19 :
    (∀ (X : Type*) [MetricSpace X] [CompleteSpace X],
      ∀ (u : ℕ → X), CauchySeq u →
        ∃ x : X, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) x < ε) := by
  intro X _ _ u hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨x, ?_⟩
  exact Metric.tendsto_atTop.mp hx
