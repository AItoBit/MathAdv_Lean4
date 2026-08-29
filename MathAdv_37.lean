import Mathlib

open Real intervalIntegral

/-- The antiderivative `F x = x/2 * (sin (log x) - cos (log x))` of `sin (log x)`. -/
noncomputable def strangF (x : ℝ) : ℝ := x / 2 * (Real.sin (Real.log x) - Real.cos (Real.log x))

/-- For `x > 0`, the derivative of `x/2 * (sin (log x) - cos (log x))` is `sin (log x)`. -/
theorem strang_7_1_13_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt strangF (Real.sin (Real.log x)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hsin : HasDerivAt (fun t => Real.sin (Real.log t))
      (Real.cos (Real.log x) * x⁻¹) x := (Real.hasDerivAt_sin _).comp x hlog
  have hcos : HasDerivAt (fun t => Real.cos (Real.log t))
      (-Real.sin (Real.log x) * x⁻¹) x := (Real.hasDerivAt_cos _).comp x hlog
  have hid : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have h2 : HasDerivAt strangF
      (1 / 2 * (Real.sin (Real.log x) - Real.cos (Real.log x))
        + x / 2 * (Real.cos (Real.log x) * x⁻¹ - -Real.sin (Real.log x) * x⁻¹)) x :=
    hid.mul (hsin.sub hcos)
  convert h2 using 1
  field_simp
  ring

/-- The integral form: for `0 < a ≤ b`, `∫ x in a..b, sin (log x) = F b - F a`. -/
theorem strang_7_1_13 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, Real.sin (Real.log x)) = strangF b - strangF a := by
  have hsub : ∀ x ∈ Set.uIcc a b, HasDerivAt strangF (Real.sin (Real.log x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact strang_7_1_13_deriv (lt_of_lt_of_le ha hx.1)
  have hcont : IntervalIntegrable (fun x => Real.sin (Real.log x)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    exact (Real.continuous_sin.continuousAt.comp (Real.continuousAt_log hx0)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hsub hcont
