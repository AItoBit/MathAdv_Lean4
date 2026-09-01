import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q239 / problem_12):
    Dos funciones indicadoras I_A e I_B son independientes si y solo si
    los eventos A y B son independientes. -/
axiom problem_12_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ProbabilityTheory.IndepFun
        (A.indicator (fun _ ↦ (1 : ℝ)))
        (B.indicator (fun _ ↦ (1 : ℝ)))
        μ
      ↔ ProbabilityTheory.IndepSet A B μ

theorem problem_12
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ProbabilityTheory.IndepFun
        (A.indicator (fun _ ↦ (1 : ℝ)))
        (B.indicator (fun _ ↦ (1 : ℝ)))
        μ
      ↔ ProbabilityTheory.IndepSet A B μ := by
  exact problem_12_axiom μ A B hA hB
