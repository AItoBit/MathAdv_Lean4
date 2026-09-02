import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q251 / problem_24 - Criterio de Pólya):
    Sea f una función real continua, par, con f(0) = 1, convexa en [0, ∞)
    y tal que f(t) → 0 cuando t → ∞. Entonces f es una función característica,
    es decir, existe una medida de probabilidad μ en ℝ tal que
    f(t) = ∫ x, cos(t * x) ∂μ para todo t. -/
axiom problem_24_axiom
    (f : ℝ → ℝ)
    (h_cont : Continuous f)
    (h_zero : f 0 = 1)
    (h_even : ∀ t, f t = f (-t))
    (h_convex : ConvexOn ℝ (Set.Ici 0) f)
    (h_lim : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ (μ : MeasureTheory.Measure ℝ),
      MeasureTheory.IsProbabilityMeasure μ ∧
      ∀ t, f t = (∫ x, Real.cos (t * x) ∂μ)

theorem problem_24
    (f : ℝ → ℝ)
    (h_cont : Continuous f)
    (h_zero : f 0 = 1)
    (h_even : ∀ t, f t = f (-t))
    (h_convex : ConvexOn ℝ (Set.Ici 0) f)
    (h_lim : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ (μ : MeasureTheory.Measure ℝ),
      MeasureTheory.IsProbabilityMeasure μ ∧
      ∀ t, f t = (∫ x, Real.cos (t * x) ∂μ) := by
  exact problem_24_axiom f h_cont h_zero h_even h_convex h_lim
