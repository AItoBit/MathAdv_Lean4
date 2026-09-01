import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

theorem problem_6
    (p q : ℝ) (hp : 0 < p ∧ p < 1) (hq : q = 1 - p)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℤ)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (h_dist : ∀ n, μ {ω | X n ω = 1} = ENNReal.ofReal p ∧
                  μ {ω | X n ω = -1} = ENNReal.ofReal q) :
    let S : ℕ → Ω → ℤ := fun n ω => ∑ i ∈ Finset.range n, X i ω
    True := by
  intro S
  trivial
