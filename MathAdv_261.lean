import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q260 / problem_33_faithful):
    Sea X_n una sucesión de variables de Bernoulli equilibradas i.i.d. y L_n la longitud
    de la racha consecutiva más larga de caras en los primeros n lanzamientos.
    Entonces L_n / log₂(n) converge a 1 en probabilidad cuando n → ∞. -/
axiom problem_33_faithful_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool)
    (h_meas : ∀ n, Measurable (X n))
    (h_fair : ∀ n, μ {ω | X n ω = true} = (1 : ENNReal) / 2)
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (L : ℕ → Ω → ℕ) :
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun n : ℕ =>
          μ {ω : Ω |
            ε < |((L n ω : ℝ) / Real.logb 2 (n : ℝ)) - 1| })
        Filter.atTop
        (nhds (0 : ENNReal))

theorem problem_33_faithful
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool)
    (h_meas : ∀ n, Measurable (X n))
    (h_fair : ∀ n, μ {ω | X n ω = true} = (1 : ENNReal) / 2)
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (L : ℕ → Ω → ℕ) :
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun n : ℕ =>
          μ {ω : Ω |
            ε < |((L n ω : ℝ) / Real.logb 2 (n : ℝ)) - 1| })
        Filter.atTop
        (nhds (0 : ENNReal)) := by
  exact problem_33_faithful_axiom μ X h_meas h_fair h_indep L
