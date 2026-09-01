import Mathlib

/-- Teorema (probabilities_4_9, Q243 / problem_16):
    Si 120 estudiantes obtienen notas no negativas con promedio 90,
    a lo sumo 60 estudiantes pueden haber obtenido una nota ≥ 180. -/
theorem problem_16
    (scores : Fin 120 → ℝ)
    (h_nonneg : ∀ i, 0 ≤ scores i)
    (h_mean : (∑ i, scores i) / 120 = 90) :
    (Finset.univ.filter (fun i => 180 ≤ scores i)).card ≤ 60 := by
  let S := Finset.univ.filter (fun i => 180 ≤ scores i)
  have h_sum_total : ∑ i, scores i = 10800 := by
    linarith [h_mean]

  -- Acotación inferior de la suma total usando los elementos del subconjunto S
  have h_sum_ge : 180 * (S.card : ℝ) ≤ ∑ i, scores i := by
    calc
      180 * (S.card : ℝ) = ∑ i ∈ S, (180 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ S, scores i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i, scores i := by
        apply Finset.sum_le_univ_sum_of_nonneg
        exact h_nonneg

  have h_card_real : (S.card : ℝ) ≤ 60 := by
    linarith [h_sum_ge, h_sum_total]

  exact_mod_cast h_card_real
