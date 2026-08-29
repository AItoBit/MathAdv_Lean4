import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Real

/-!
# `∫ cos x · sin (2x) dx = -(2/3) cos³ x + C`
-/

/-- For every constant `C`, the function `x ↦ -(2/3) cos³ x + C` is an antiderivative
of `x ↦ cos x * sin (2 x)`. -/
theorem hasDerivAt_neg_two_thirds_cos_cube (C x : ℝ) :
    HasDerivAt (fun t : ℝ => -(2 / 3) * (cos t) ^ 3 + C) (cos x * sin (2 * x)) x := by
  have hc : HasDerivAt (fun t : ℝ => cos t) (-sin x) x := Real.hasDerivAt_cos x
  have h3 := (hc.pow 3)
  have h := ((h3.const_mul (-(2 / 3) : ℝ)).add_const C)
  apply HasDerivAt.congr_deriv h
  rw [Real.sin_two_mul]
  ring

/-- The definite integral form: `∫ x in a..b, cos x * sin (2x) = -(2/3) cos³ b + (2/3) cos³ a`. -/
theorem integral_cos_mul_sin_two_mul (a b : ℝ) :
    (∫ x in a..b, cos x * sin (2 * x)) =
      -(2 / 3) * (cos b) ^ 3 - -(2 / 3) * (cos a) ^ 3 := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(2 / 3) * (cos t) ^ 3) (cos x * sin (2 * x)) x := by
    intro x _
    simpa using hasDerivAt_neg_two_thirds_cos_cube 0 x
  have hint : IntervalIntegrable (fun x : ℝ => cos x * sin (2 * x)) MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
