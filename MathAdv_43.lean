import Mathlib

open scoped Topology
open Filter

/-- On `[a, 1]` with `0 < a ≤ 1`, the antiderivative of `log x / x` is `(log x)^2 / 2`,
so `∫_a^1 log x / x dx = -(log a)^2 / 2`. -/
theorem integral_log_div_self (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in a..1, Real.log x / x) = -(Real.log a) ^ 2 / 2 := by
  have hsub : Set.uIcc a 1 ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le ha1]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ Set.uIcc a 1,
      HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log x / x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hsub hx)
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 := (h1.pow 2).div_const 2
    apply HasDerivAt.congr_deriv h2
    simp only [div_eq_mul_inv]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x) MeasureTheory.volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hsub hx)
    exact ((Real.continuousAt_log hx0).continuousWithinAt).div
      continuousWithinAt_id (by simpa using hx0)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Real.log_one] at key
  rw [key]
  ring

/-- The integral `∫₀¹ (log x)/x dx` diverges: `∫_a^1 (log x)/x dx → -∞` as `a → 0⁺`. -/
theorem strang_7_5_7 :
    Filter.Tendsto (fun a => ∫ x in a..1, Real.log x / x) (𝓝[>] 0) Filter.atBot := by
  have h : Tendsto (fun a : ℝ => -Real.log a) (𝓝[>] (0:ℝ)) atTop :=
    Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h2 : Tendsto (fun a : ℝ => (Real.log a) ^ 2) (𝓝[>] (0:ℝ)) atTop := by
    simpa [sq] using h.atTop_mul_atTop₀ h
  have h3 : Tendsto (fun a : ℝ => (Real.log a) ^ 2 / 2) (𝓝[>] (0:ℝ)) atTop :=
    h2.atTop_div_const (by norm_num)
  have hsq : Tendsto (fun a : ℝ => -(Real.log a) ^ 2 / 2) (𝓝[>] (0:ℝ)) atBot :=
    (Filter.tendsto_neg_atTop_atBot.comp h3).congr (fun x => by simp [neg_div])
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with a ha ha1
  exact (integral_log_div_self a ha (le_of_lt ha1)).symm
