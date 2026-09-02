import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q253 / problem_26):
    Sea X una variable con distribución Uniforme en [0, 1]. El evento B de que el
    dígito 7 aparezca infinitas veces en el desarrollo decimal de X tiene probabilidad 1. -/
axiom problem_26_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      P {ω | a ≤ X ω ∧ X ω ≤ b} = ENNReal.ofReal (b - a)) :
    let A : ℕ → Set Ω := fun n => {ω | ⌊(10 : ℝ) ^ n * X ω⌋ % 10 = 7}
    let B : Set Ω := {ω | Set.Infinite {n | ω ∈ A n}}
    P B = 1

theorem problem_26
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      P {ω | a ≤ X ω ∧ X ω ≤ b} = ENNReal.ofReal (b - a)) :
    let A : ℕ → Set Ω := fun n => {ω | ⌊(10 : ℝ) ^ n * X ω⌋ % 10 = 7}
    let B : Set Ω := {ω | Set.Infinite {n | ω ∈ A n}}
    P B = 1 := by
  exact problem_26_axiom X hX
