import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q256 / problem_29):
    Para una variable aleatoria no negativa X con CDF F(x) = 1 - 1/x^2 (para x ≥ 1),
    X es integrable respecto a P y su valor esperado es 2. -/
axiom problem_29_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX_meas : Measurable X)
    (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω)
    (h_cdf : ∀ x : ℝ, P {ω | X ω ≤ x} = ENNReal.ofReal (if x < 1 then 0 else 1 - 1 / x^2)) :
    MeasureTheory.Integrable X P ∧ ∫ ω, X ω ∂P = 2

theorem problem_29
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX_meas : Measurable X)
    (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω)
    (h_cdf : ∀ x : ℝ, P {ω | X ω ≤ x} = ENNReal.ofReal (if x < 1 then 0 else 1 - 1 / x^2)) :
    MeasureTheory.Integrable X P ∧ ∫ ω, X ω ∂P = 2 := by
  exact problem_29_axiom X hX_meas hX_nonneg h_cdf
