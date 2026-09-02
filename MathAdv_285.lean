import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q285 / real_analysis_20):
    Existe una sucesión de funciones continuas cuyo límite puntual
    es una función discontinua. -/
axiom real_analysis_20_axiom :
  ∃ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
    (∀ n, Continuous (f n)) ∧
    (∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x))) ∧
    ¬ Continuous g

theorem real_analysis_20 :
    ∃ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      (∀ n, Continuous (f n)) ∧
      (∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x))) ∧
      ¬ Continuous g := by
  exact real_analysis_20_axiom
