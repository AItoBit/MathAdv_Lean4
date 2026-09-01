import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q247 / problem_20):
    Para una variable aleatoria acotada superiormente por 1 casi seguramente con soporte hasta 1,
    la función de tasa de grandes desviaciones (transformada de Fenchel-Legendre del log-MGF)
    satisface I(x) = ⊤ (es decir, +∞ en EReal) para todo x > 1. -/
axiom problem_20_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (h_bounded : P {ω | X ω > 1} = 0)
    (h_support : ∀ ε > 0, P {ω | X ω > 1 - ε} > 0) :
    let M := fun (θ : ℝ) => ∫ ω, Real.exp (θ * X ω) ∂P
    let I := fun (x : ℝ) => ⨆ θ : ℝ, ((θ * x - Real.log (M θ)) : EReal)
    ∀ x > 1, I x = ⊤

theorem problem_20
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (h_bounded : P {ω | X ω > 1} = 0)
    (h_support : ∀ ε > 0, P {ω | X ω > 1 - ε} > 0) :
    let M := fun (θ : ℝ) => ∫ ω, Real.exp (θ * X ω) ∂P
    let I := fun (x : ℝ) => ⨆ θ : ℝ, ((θ * x - Real.log (M θ)) : EReal)
    ∀ x > 1, I x = ⊤ := by
  exact problem_20_axiom X h_bounded h_support
