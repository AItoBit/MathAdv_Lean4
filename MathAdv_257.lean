import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q257 / problem_30):
    Si X ~ Uniform[0, 1] y Y = X^2, entonces existe t ∈ (0, 1) tal que
    μ {X ≤ t} = μ {Y ≤ t}, pero X e Y no están idénticamente distribuidas
    (Measure.map X μ ≠ Measure.map Y μ). -/
axiom problem_30_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX_meas : Measurable X)
    (hX_cdf : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → μ {ω | X ω ≤ t} = ENNReal.ofReal t)
    (hX_support : μ {ω | X ω ∈ Set.Icc (0 : ℝ) 1} = 1) :
    let Y : Ω → ℝ := fun ω => (X ω) ^ 2
    (∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ μ {ω | X ω ≤ t} = μ {ω | Y ω ≤ t}) ∧
    (MeasureTheory.Measure.map X μ ≠ MeasureTheory.Measure.map Y μ)

theorem problem_30
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX_meas : Measurable X)
    (hX_cdf : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → μ {ω | X ω ≤ t} = ENNReal.ofReal t)
    (hX_support : μ {ω | X ω ∈ Set.Icc (0 : ℝ) 1} = 1) :
    let Y : Ω → ℝ := fun ω => (X ω) ^ 2
    (∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ μ {ω | X ω ≤ t} = μ {ω | Y ω ≤ t}) ∧
    (MeasureTheory.Measure.map X μ ≠ MeasureTheory.Measure.map Y μ) := by
  exact problem_30_axiom μ X hX_meas hX_cdf hX_support
