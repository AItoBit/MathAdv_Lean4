import Mathlib

theorem real_analysis_24 :
  ∃ x : ℕ → ℝ,
    (∀ n, 1 ≤ n → |x (n + 1) - x n| < 1 / (2 * Real.sqrt n)) ∧
    ¬ CauchySeq x := by

  refine ⟨fun n : ℕ => Real.sqrt (n : ℝ), ?_, ?_⟩

  · intro n hn

    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn

    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) :=
      le_of_lt hn_pos

    have hsqrt_pos :
        0 < Real.sqrt (n : ℝ) := by
      exact Real.sqrt_pos.2 hn_pos

    have harg :
        (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self n

    have hsqrt_lt :
        Real.sqrt (n : ℝ) <
          Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      exact Real.sqrt_lt_sqrt hn_nonneg harg

    have hsquare_n :
        (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
      exact Real.sq_sqrt hn_nonneg

    have hsquare_succ :
        (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 =
          ((n + 1 : ℕ) : ℝ) := by
      exact Real.sq_sqrt (by positivity)

    have hprod :
        (Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) +
            Real.sqrt (n : ℝ)) = 1 := by
      calc
        (Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) +
            Real.sqrt (n : ℝ))
            =
          (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 -
            (Real.sqrt (n : ℝ)) ^ 2 := by
              ring
        _ = ((n + 1 : ℕ) : ℝ) - (n : ℝ) := by
              rw [hsquare_succ, hsquare_n]
        _ = 1 := by
              norm_num

    have hdiff_pos :
        0 <
          Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) := by
      linarith

    rw [abs_of_pos hdiff_pos]

    apply
      (lt_div_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt_pos)).2

    have hden :
        2 * Real.sqrt (n : ℝ) <
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
            Real.sqrt (n : ℝ) := by
      linarith

    calc
      (Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ)) *
          (2 * Real.sqrt (n : ℝ))
          <
        (Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) +
            Real.sqrt (n : ℝ)) := by
              exact mul_lt_mul_of_pos_left hden hdiff_pos
      _ = 1 := hprod

  · intro hc

    obtain ⟨R, hR_pos, hR⟩ :=
      cauchySeq_bdd hc

    obtain ⟨k, hk⟩ :=
      exists_nat_gt R

    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
      positivity

    have hsqrt_square :
        Real.sqrt (((k ^ 2 : ℕ) : ℝ)) = (k : ℝ) := by
      rw [Nat.cast_pow]
      exact Real.sqrt_sq hk_nonneg

    have hb :=
      hR (k ^ 2) 0

    have hb' : (k : ℝ) < R := by
      simpa [
        Real.dist_eq,
        hsqrt_square,
        abs_of_nonneg hk_nonneg
      ] using hb

    linarith
