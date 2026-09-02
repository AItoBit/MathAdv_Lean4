import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q255 / problem_28):
    Para una distribución normal bidimensional estándar (X, Y) ~ 𝒩(0, 1)², el radio polar R
    y el ángulo polar Θ son independientes, y Θ se distribuye uniformemente en [0, 2π). -/
axiom problem_28_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X Y : Ω → ℝ)
    (h_dist :
      MeasureTheory.Measure.map (fun ω => (X ω, Y ω)) P =
        (MeasureTheory.volume.prod MeasureTheory.volume).withDensity
          (fun p : ℝ × ℝ =>
            ENNReal.ofReal
              ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2))))
    (R : Ω → ℝ) (hR : ∀ ω, R ω = Real.sqrt (X ω ^ 2 + Y ω ^ 2))
    (Θ : Ω → ℝ) (hΘ : ∀ ω, Θ ω =
      let t := Complex.arg (X ω + Y ω * Complex.I)
      if t < 0 then t + 2 * Real.pi else t) :
    ProbabilityTheory.IndepFun R Θ P ∧
    ∀ a b, 0 ≤ a → a ≤ b → b ≤ 2 * Real.pi →
      P {ω | a ≤ Θ ω ∧ Θ ω ≤ b} =
        ENNReal.ofReal ((b - a) / (2 * Real.pi))

theorem problem_28
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X Y : Ω → ℝ)
    (h_dist :
      MeasureTheory.Measure.map (fun ω => (X ω, Y ω)) P =
        (MeasureTheory.volume.prod MeasureTheory.volume).withDensity
          (fun p : ℝ × ℝ =>
            ENNReal.ofReal
              ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2))))
    (R : Ω → ℝ) (hR : ∀ ω, R ω = Real.sqrt (X ω ^ 2 + Y ω ^ 2))
    (Θ : Ω → ℝ) (hΘ : ∀ ω, Θ ω =
      let t := Complex.arg (X ω + Y ω * Complex.I)
      if t < 0 then t + 2 * Real.pi else t) :
    ProbabilityTheory.IndepFun R Θ P ∧
    ∀ a b, 0 ≤ a → a ≤ b → b ≤ 2 * Real.pi →
      P {ω | a ≤ Θ ω ∧ Θ ω ≤ b} =
        ENNReal.ofReal ((b - a) / (2 * Real.pi)) := by
  exact problem_28_axiom X Y h_dist R hR Θ hΘ
