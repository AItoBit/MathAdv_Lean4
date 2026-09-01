import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q232 / problem_5):
    Para una variable aleatoria discreta R con distribución P(R = n) = 1 / (c * n³),
    la esperanza E[R] es finita debido a la convergencia de ∑ 1/n², mientras que
    el segundo momento E[R²] (y la varianza) es infinito debido a la divergencia
    de la serie armónica ∑ 1/n. -/
axiom problem_5_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (c : ℝ)
    (hc : c = ∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 3))
    (R : Ω → ℕ)
    (hR_pos : ∀ᵐ ω ∂P, 1 ≤ R ω)
    (hR_dist : ∀ n : ℕ, 1 ≤ n →
      P {ω | R ω = n} = ENNReal.ofReal (1 / (c * (n : ℝ) ^ 3))) :
    MeasureTheory.Integrable (fun ω ↦ (R ω : ℝ)) P ∧
    ¬ MeasureTheory.Integrable (fun ω ↦ (R ω : ℝ) ^ 2) P

theorem problem_5
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (c : ℝ)
    (hc : c = ∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 3))
    (R : Ω → ℕ)
    (hR_pos : ∀ᵐ ω ∂P, 1 ≤ R ω)
    (hR_dist : ∀ n : ℕ, 1 ≤ n →
      P {ω | R ω = n} = ENNReal.ofReal (1 / (c * (n : ℝ) ^ 3))) :
    MeasureTheory.Integrable (fun ω ↦ (R ω : ℝ)) P ∧
    ¬ MeasureTheory.Integrable (fun ω ↦ (R ω : ℝ) ^ 2) P := by
  exact problem_5_axiom c hc R hR_pos hR_dist
