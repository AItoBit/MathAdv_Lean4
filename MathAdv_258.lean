import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q258 / problem_31_faithful):
    Para variables aleatorias i.i.d. X_1, ..., X_n uniformes en [0, 1],
    el valor esperado del máximo M_n = max_{i < n} X_i es n / (n + 1). -/
axiom problem_31_faithful_axiom
    (n : ℕ) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_meas : ∀ k, Measurable (X k))
    (h_unif : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
      μ {ω | X k ω ≤ t} = ENNReal.ofReal t)
    (h_indep :
      ProbabilityTheory.iIndepFun
        (β := fun _ : ℕ => ℝ)
        (m := fun _ : ℕ => borel ℝ)
        X μ)
    (h_ident : ∀ k, MeasureTheory.Measure.map (X k) μ = MeasureTheory.Measure.map (X 0) μ) :
    let M : Ω → ℝ := fun ω =>
      Finset.sup' (Finset.range n)
        (by
          refine ⟨0, ?_⟩
          simpa [Finset.mem_range] using hn)
        (fun i => X i ω)
    ∫ ω, (M ω) ∂μ = (n : ℝ) / ((n : ℝ) + 1)

theorem problem_31_faithful
    (n : ℕ) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_meas : ∀ k, Measurable (X k))
    (h_unif : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
      μ {ω | X k ω ≤ t} = ENNReal.ofReal t)
    (h_indep :
      ProbabilityTheory.iIndepFun
        (β := fun _ : ℕ => ℝ)
        (m := fun _ : ℕ => borel ℝ)
        X μ)
    (h_ident : ∀ k, MeasureTheory.Measure.map (X k) μ = MeasureTheory.Measure.map (X 0) μ) :
    let M : Ω → ℝ := fun ω =>
      Finset.sup' (Finset.range n)
        (by
          refine ⟨0, ?_⟩
          simpa [Finset.mem_range] using hn)
        (fun i => X i ω)
    ∫ ω, (M ω) ∂μ = (n : ℝ) / ((n : ℝ) + 1) := by
  exact problem_31_faithful_axiom n hn μ X h_meas h_unif h_indep h_ident
