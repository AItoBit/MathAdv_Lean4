import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory intervalIntegral

/-! # Fourier sine coefficients: `C = 4 / (3π)`

If `A sin x + B sin 2x + C sin 3x + ⋯ = 1` on `(0, π)`, then multiplying by `sin 3x`
and integrating over `[0, π]` isolates `C` by orthogonality of the sine functions:
`C · (π/2) = ∫₀^π sin 3x dx = 2/3`, hence `C = 4/(3π)`. -/

/-- `∫₀^π cos (k x) dx = π` if `k = 0` and `0` otherwise, for an integer `k`. -/
lemma integral_cos_int_mul (k : ℤ) :
    (∫ x in (0:ℝ)..π, Real.cos (k * x)) = if k = 0 then π else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    rw [if_neg hk]
    rw [intervalIntegral.integral_comp_mul_left (c := (k : ℝ)) Real.cos hk']
    rw [integral_cos]
    have : Real.sin ((k : ℝ) * π) = 0 := Real.sin_int_mul_pi k
    simp [this]

/-- Orthogonality of the sine system on `[0, π]`. -/
lemma integral_sin_mul_sin_pi (m n : ℕ) :
    (∫ x in (0:ℝ)..π, Real.sin (m * x) * Real.sin (n * x))
      = if m = n ∧ m ≠ 0 then π / 2 else 0 := by
  have key : ∀ x : ℝ, Real.sin (m * x) * Real.sin (n * x)
      = (Real.cos (((m : ℤ) - n : ℤ) * x) - Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
    intro x
    have h1 : ((((m : ℤ) - n : ℤ) : ℝ) * x) = (m : ℝ) * x - (n : ℝ) * x := by push_cast; ring
    have h2 : ((((m : ℤ) + n : ℤ) : ℝ) * x) = (m : ℝ) * x + (n : ℝ) * x := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hint1 : IntervalIntegrable (fun x : ℝ => Real.cos (((m : ℤ) - n : ℤ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => Real.cos (((m : ℤ) + n : ℤ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous _).intervalIntegrable _ _
  calc (∫ x in (0:ℝ)..π, Real.sin (m * x) * Real.sin (n * x))
      = ∫ x in (0:ℝ)..π,
          (Real.cos (((m : ℤ) - n : ℤ) * x) - Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
        simp_rw [key]
    _ = ((∫ x in (0:ℝ)..π, Real.cos (((m : ℤ) - n : ℤ) * x))
          - ∫ x in (0:ℝ)..π, Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hint1 hint2]
    _ = if m = n ∧ m ≠ 0 then π / 2 else 0 := by
        rw [integral_cos_int_mul, integral_cos_int_mul]
        by_cases hmn : m = n
        · subst hmn
          by_cases hm : m = 0
          · subst hm; norm_num
          · have h1 : ((m : ℤ) - m : ℤ) = 0 := by ring
            have h2 : ((m : ℤ) + m : ℤ) ≠ 0 := by
              simpa using hm
            rw [if_pos h1, if_neg h2, if_pos ⟨rfl, hm⟩]
            ring
        · have h1 : ((m : ℤ) - n : ℤ) ≠ 0 := by
            simpa [sub_eq_zero] using fun h => hmn (by exact_mod_cast h)
          have h2 : ((m : ℤ) + n : ℤ) ≠ 0 := by
            rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm
              simp only [Nat.cast_zero, zero_add, ne_eq, Nat.cast_eq_zero]
              omega
            · positivity
          rw [if_neg h1, if_neg h2, if_neg (by tauto)]
          ring

/-- `∫₀^π sin (3x) dx = 2/3`. -/
lemma integral_sin_three : (∫ x in (0:ℝ)..π, Real.sin (3 * x)) = 2 / 3 := by
  rw [intervalIntegral.integral_comp_mul_left (c := (3:ℝ)) Real.sin (by norm_num), integral_sin]
  have h3 : Real.cos (3 * π) = -1 := by
    have : (3:ℝ) * π = π + 2 * π := by ring
    rw [this, Real.cos_add_two_pi, Real.cos_pi]
  rw [h3]
  norm_num

/-- **Main result.** If an absolutely convergent sine series `∑ aₙ sin (n x)` equals `1`
on `(0, π)`, then its third coefficient is `4 / (3π)`.

This is the formal version of "multiply by `sin 3x` and integrate from `0` to `π`":
orthogonality kills every term except `n = 3`. -/
theorem fourier_sine_coeff_three (a : ℕ → ℝ) (ha : Summable a)
    (h : ∀ x ∈ Set.Ioo (0:ℝ) π, ∑' n, a n * Real.sin (n * x) = 1) :
    a 3 = 4 / (3 * π) := by
  set F : ℕ → ℝ → ℝ := fun n x => a n * Real.sin (n * x) * Real.sin (3 * x) with hF
  have hpi : (0:ℝ) ≤ π := Real.pi_pos.le
  -- each `F n` is integrable on `Ioc 0 π`
  have hFint : ∀ n, IntegrableOn (F n) (Set.Ioc (0:ℝ) π) MeasureTheory.volume := by
    intro n
    exact (by fun_prop : Continuous (F n)).integrableOn_Ioc
  -- the integrals of the norms are summable
  have hnormbd : ∀ n, (∫ x in Set.Ioc (0:ℝ) π, ‖F n x‖) ≤ |a n| * π := by
    intro n
    have hle : ∀ x : ℝ, ‖F n x‖ ≤ |a n| := by
      intro x
      have h1 : |Real.sin ((n : ℝ) * x)| ≤ 1 := Real.abs_sin_le_one _
      have h2 : |Real.sin (3 * x)| ≤ 1 := Real.abs_sin_le_one _
      calc ‖F n x‖ = |a n| * |Real.sin ((n : ℝ) * x)| * |Real.sin (3 * x)| := by
            simp [hF, Real.norm_eq_abs]
        _ ≤ |a n| * 1 * 1 := by
            gcongr
        _ = |a n| := by ring
    have hcalc : (∫ _x in Set.Ioc (0:ℝ) π, |a n|) = |a n| * π := by
      rw [MeasureTheory.setIntegral_const]
      simp [max_eq_left hpi, mul_comm]
    calc (∫ x in Set.Ioc (0:ℝ) π, ‖F n x‖)
        ≤ ∫ _x in Set.Ioc (0:ℝ) π, |a n| := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards with x using norm_nonneg _
          · exact (continuous_const).integrableOn_Ioc
          · filter_upwards with x using hle x
      _ = |a n| * π := hcalc
  have hsummable : Summable fun n => ∫ x in Set.Ioc (0:ℝ) π, ‖F n x‖ := by
    have habs : Summable fun n => |a n| * π := (summable_abs_iff.2 ha).mul_right π
    refine Summable.of_nonneg_of_le (fun n => ?_) hnormbd habs
    exact MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
  -- interchange sum and integral
  have hswap : (∑' n, ∫ x in Set.Ioc (0:ℝ) π, F n x)
      = ∫ x in Set.Ioc (0:ℝ) π, ∑' n, F n x :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsummable
  -- compute the individual integrals
  have hterm : ∀ n, (∫ x in Set.Ioc (0:ℝ) π, F n x)
      = a n * (if n = 3 ∧ n ≠ 0 then π / 2 else 0) := by
    intro n
    rw [← intervalIntegral.integral_of_le hpi]
    rw [show (fun x => F n x) = fun x => a n * (Real.sin (n * x) * Real.sin (3 * x)) by
      funext x; simp [hF]; ring]
    rw [intervalIntegral.integral_const_mul]
    have h3 : ∀ x : ℝ, Real.sin (3 * x) = Real.sin (((3 : ℕ) : ℝ) * x) := by
      intro x; norm_num
    simp_rw [h3]
    rw [integral_sin_mul_sin_pi n 3]
  have hleft : (∑' n, ∫ x in Set.Ioc (0:ℝ) π, F n x) = a 3 * (π / 2) := by
    rw [tsum_eq_single 3]
    · rw [hterm 3]; norm_num
    · intro n hn
      rw [hterm n, if_neg (by tauto), mul_zero]
  -- compute the right-hand integral
  have hright : (∫ x in Set.Ioc (0:ℝ) π, ∑' n, F n x) = 2 / 3 := by
    rw [← intervalIntegral.integral_of_le hpi, ← integral_sin_three]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le hpi] at hx
    show ∑' n, F n x = Real.sin (3 * x)
    have hxs : ∑' n, F n x = (∑' n, a n * Real.sin (n * x)) * Real.sin (3 * x) := by
      simp only [hF]
      exact tsum_mul_right
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rw [hxs, ← h0]
      norm_num
    rcases eq_or_lt_of_le hx.2 with h1 | h1
    · have hs : Real.sin (3 * x) = 0 := by
        rw [h1, show (3:ℝ) * π = π + 2 * π by ring, Real.sin_add_two_pi, Real.sin_pi]
      rw [hxs, hs, mul_zero]
    · rw [hxs, h x ⟨h0, h1⟩, one_mul]
  -- conclude
  have hfin : a 3 * (π / 2) = 2 / 3 := by rw [← hleft, hswap, hright]
  have hpi' : π ≠ 0 := Real.pi_ne_zero
  field_simp at hfin ⊢
  linarith

/-!
The statement as originally posed quantifies over the closed interval `[0, π]`.
At `x = 0` (and at `x = π`) every term `aₙ sin (n x)` vanishes, so the hypothesis
asserts `0 = 1` there; it is therefore contradictory and the conclusion follows
vacuously.  The mathematically meaningful version is `fourier_sine_coeff_three`
above, which assumes the identity on the open interval `(0, π)` together with
absolute convergence of the coefficients (enough to integrate term by term).
-/
theorem strang_7_2_34
    (a : ℕ → ℝ)
    (h : ∀ x ∈ Set.Icc 0 Real.pi, ∑' n, a n * Real.sin (n * x) = 1) :
    a 3 = 4 / (3 * Real.pi) := by
  have h0 := h 0 ⟨le_refl 0, Real.pi_pos.le⟩
  simp at h0
