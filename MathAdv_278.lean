import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q278 / real_analysis_13):
    Representación del funcional integral como integración respecto a una medida
    (Teorema de Representación de Riesz-Markov). -/
theorem real_analysis_13 :
    ∃ μ : MeasureTheory.Measure ℝ, ∀ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc (0 : ℝ) 1) →
      (∫ x in Set.Icc (0 : ℝ) 1, f x) = ∫ x, f x ∂μ := by
  use volume.restrict (Set.Icc (0 : ℝ) 1)
  intro f _
  rfl
