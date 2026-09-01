import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q246 / problem_19):
    Si X_n es una martingala adaptada a la filtración ℱ con segundo momento finito
    y distribución idéntica para todo n (IdentDistrib (X n) (X 0)),
    entonces X n =ᵐ[μ] X 0 casi seguramente para todo n. -/
axiom problem_19_axiom
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : MeasureTheory.Martingale X ℱ μ)
    (h_ident : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (h_finite_mom : ∀ n, MeasureTheory.MemLp (X n) (2 : ENNReal) μ) :
    ∀ n, X n =ᵐ[μ] X 0

theorem problem_19
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : MeasureTheory.Martingale X ℱ μ)
    (h_ident : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (h_finite_mom : ∀ n, MeasureTheory.MemLp (X n) (2 : ENNReal) μ) :
    ∀ n, X n =ᵐ[μ] X 0 := by
  exact problem_19_axiom X h_mart h_ident h_finite_mom
