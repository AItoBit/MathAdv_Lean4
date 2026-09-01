import Mathlib

/-- Teorema (probabilities_4_9, Q240 / problem_13):
    La probabilidad de que como máximo 200 de las 215 reservas se presenten
    (cada una con probabilidad p = 0.9) es aproximadamente 0.95 (con error < 0.01). -/
theorem problem_13 :
    let n := 215
    let k := 200
    let p_show : ℝ := 1 - 0.1
    let prob_m_show (m : ℕ) : ℝ :=
      (Nat.choose n m : ℝ) * (p_show ^ m) * ((1 - p_show) ^ (n - m))
    let prob_all_get_rooms : ℝ :=
      ∑ m ∈ Finset.range (k + 1), prob_m_show m
    dist prob_all_get_rooms 0.95 < 0.01 := by
  intro n k p_show prob_m_show prob_all_get_rooms
  dsimp [prob_all_get_rooms, prob_m_show, p_show, n, k]

  have hp : (1 - 0.1 : ℝ) = ((9 / 10 : ℚ) : ℝ) := by norm_num
  have hq : (1 - (1 - 0.1) : ℝ) = ((1 / 10 : ℚ) : ℝ) := by norm_num
  have h95 : (0.95 : ℝ) = ((95 / 100 : ℚ) : ℝ) := by norm_num
  have h01 : (0.01 : ℝ) = ((1 / 100 : ℚ) : ℝ) := by norm_num

  rw [hp, hq, h95, h01, Real.dist_eq]

  have h_sum_cast : (∑ m ∈ Finset.range 201,
      (Nat.choose 215 m : ℝ) * (((9 / 10 : ℚ) : ℝ) ^ m) * (((1 / 10 : ℚ) : ℝ) ^ (215 - m)))
    = ((∑ m ∈ Finset.range 201,
      (Nat.choose 215 m : ℚ) * ((9 / 10 : ℚ) ^ m) * ((1 / 10 : ℚ) ^ (215 - m)) : ℚ) : ℝ) := by
    push_cast
    rfl

  rw [h_sum_cast]
  have h_bound : |(∑ m ∈ Finset.range 201,
      (Nat.choose 215 m : ℚ) * ((9 / 10 : ℚ) ^ m) * ((1 / 10 : ℚ) ^ (215 - m))) - (95 / 100 : ℚ)| < (1 / 100 : ℚ) := by
    decide

  exact_mod_cast h_bound
