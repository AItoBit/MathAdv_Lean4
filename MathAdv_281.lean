import Mathlib

theorem real_analysis_16 :
  ∃ f : ℝ → ℝ,
    (∀ ⦃u v : ℝ⦄, u ≠ v → |f u - f v| < |u - v|) ∧
    ¬ ∃ x : ℝ, f x = x := by

  refine ⟨fun x => Real.sqrt (x ^ 2 + 1), ?_, ?_⟩

  · intro u v huv

    let a : ℝ := Real.sqrt (u ^ 2 + 1)
    let b : ℝ := Real.sqrt (v ^ 2 + 1)

    change |a - b| < |u - v|

    have hua : |u| < a := by
      calc
        |u| = Real.sqrt (u ^ 2) := by
          symm
          exact Real.sqrt_sq_eq_abs u
        _ < Real.sqrt (u ^ 2 + 1) := by
          apply Real.sqrt_lt_sqrt
          · exact sq_nonneg u
          · linarith
        _ = a := by
          rfl

    have hvb : |v| < b := by
      calc
        |v| = Real.sqrt (v ^ 2) := by
          symm
          exact Real.sqrt_sq_eq_abs v
        _ < Real.sqrt (v ^ 2 + 1) := by
          apply Real.sqrt_lt_sqrt
          · exact sq_nonneg v
          · linarith
        _ = b := by
          rfl

    have hab_nonneg : 0 ≤ a + b := by
      apply add_nonneg
      · dsimp [a]
        exact Real.sqrt_nonneg _
      · dsimp [b]
        exact Real.sqrt_nonneg _

    have huv_sum : |u + v| < a + b := by
      calc
        |u + v| ≤ |u| + |v| := by
          exact abs_add_le u v
        _ < a + b := by
          exact add_lt_add hua hvb

    have ha_sq : a ^ 2 = u ^ 2 + 1 := by
      dsimp [a]
      exact Real.sq_sqrt (by positivity)

    have hb_sq : b ^ 2 = v ^ 2 + 1 := by
      dsimp [b]
      exact Real.sq_sqrt (by positivity)

    have hprod :
        (a - b) * (a + b) =
          (u - v) * (u + v) := by
      nlinarith [ha_sq, hb_sq]

    have habsprod :
        |a - b| * (a + b) =
          |u - v| * |u + v| := by
      have h := congrArg abs hprod
      rw [abs_mul, abs_mul] at h
      rw [abs_of_nonneg hab_nonneg] at h
      exact h

    have huv_pos : 0 < |u - v| := by
      exact abs_pos.mpr (sub_ne_zero.mpr huv)

    by_contra hlt

    have hge : |u - v| ≤ |a - b| := by
      exact le_of_not_gt hlt

    have hmul :
        |u - v| * (a + b) ≤
          |a - b| * (a + b) := by
      exact mul_le_mul_of_nonneg_right hge hab_nonneg

    rw [habsprod] at hmul

    have hbad : a + b ≤ |u + v| := by
      nlinarith

    exact (not_le_of_gt huv_sum) hbad

  · rintro ⟨x, hx⟩

    change Real.sqrt (x ^ 2 + 1) = x at hx

    by_cases hx_nonneg : 0 ≤ x

    · have hlt :
          x < Real.sqrt (x ^ 2 + 1) := by
        apply (Real.lt_sqrt hx_nonneg).2
        linarith

      linarith

    · have hx_neg : x < 0 := by
        exact lt_of_not_ge hx_nonneg

      have hsqrt_nonneg :
          0 ≤ Real.sqrt (x ^ 2 + 1) :=
        Real.sqrt_nonneg _

      linarith
