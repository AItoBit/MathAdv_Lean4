import Mathlib

set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q241 / problem_14):
    El valor de p ∈ (0, 1) que minimiza E[N_TTH] = 1 / (p * (1 - p)^2) es p = 1/3. -/
theorem problem_14
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (h_dist : ∀ n, μ {ω | X n ω = true} = ENNReal.ofReal p) :
    ∀ p' : ℝ, 0 < p' ∧ p' < 1 →
      (1 : ℝ) / ((1 / 3 : ℝ) * (1 - 1 / 3 : ℝ)^2) ≤
        (1 : ℝ) / (p' * (1 - p')^2) := by
  intro p' ⟨hp'_pos, hp'_lt_one⟩

  -- 1) Identidad algebraica exacta
  have h_diff : (4 / 27 : ℝ) - p' * (1 - p')^2 = (3 * p' - 1)^2 * (4 - 3 * p') / 27 := by
    ring

  have h_diff_nonneg : 0 ≤ (4 / 27 : ℝ) - p' * (1 - p')^2 := by
    rw [h_diff]
    have _h_sq : 0 ≤ (3 * p' - 1)^2 := sq_nonneg (3 * p' - 1)
    have _h_lin : 0 ≤ 4 - 3 * p' := by linarith
    positivity

  have h_le_max : p' * (1 - p')^2 ≤ 4 / 27 := by
    linarith

  have h_pos : 0 < p' * (1 - p')^2 := by
    have h_sub_pos : 0 < 1 - p' := by linarith
    have h_sub_sq : 0 < (1 - p')^2 := sq_pos_of_pos h_sub_pos
    exact mul_pos hp'_pos h_sub_sq

  have h_third : (1 / 3 : ℝ) * (1 - 1 / 3 : ℝ)^2 = 4 / 27 := by
    ring

  rw [h_third]
  exact one_div_le_one_div_of_le h_pos h_le_max
