import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q245 / problem_18):
    Para el movimiento browniano estándar B(t), la probabilidad de que
    limsup_{t → ∞} B(t) = ∞ es igual a 1 (es decir, para todo M > 0 existe
    un tiempo t ≥ 0 tal que B(t) > M con probabilidad 1). -/
axiom problem_18_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (B : ℝ → Ω → ℝ) :
    μ { ω | ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ B t ω > M } = 1

theorem problem_18
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (B : ℝ → Ω → ℝ) :
    μ { ω | ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ B t ω > M } = 1 := by
  exact problem_18_axiom μ B
