import Mathlib

open Real intervalIntegral

/-- The antiderivative `F x = -½ e^{x⁶ - 5x²} + C`. -/
noncomputable def dawkinsF (C : ℝ) (x : ℝ) : ℝ := -1 / 2 * exp (x ^ 6 - 5 * x ^ 2) + C

/-- `x ↦ -½ e^{x⁶ - 5x²} + C` is an antiderivative of `(5x - 3x⁵) e^{x⁶ - 5x²}`. -/
theorem hasDerivAt_dawkinsF (C x : ℝ) :
    HasDerivAt (dawkinsF C) ((5 * x - 3 * x ^ 5) * exp (x ^ 6 - 5 * x ^ 2)) x := by
  -- 1. Inner derivative of u(x) = x^6 - 5*x^2
  have h_pow6 := hasDerivAt_pow 6 x
  have h_pow2 := (hasDerivAt_pow 2 x).const_mul (5 : ℝ)
  have hu : HasDerivAt (fun x : ℝ => x ^ 6 - 5 * x ^ 2) (6 * x ^ 5 - 10 * x) x := by
    apply HasDerivAt.congr_deriv (h_pow6.sub h_pow2)
    ring

  -- 2. Differentiate the full expression (-1/2 * exp(u(x)) + C)
  have h := ((hu.exp).const_mul (-1 / 2 : ℝ)).add_const C

  -- 3. Equate with the target derivative
  apply HasDerivAt.congr_deriv h
  ring

/-- Fundamental theorem of calculus form: the definite integral of
`(5x - 3x⁵) e^{x⁶ - 5x²}` over `[a, b]` is `F b - F a`, where
`F x = -½ e^{x⁶ - 5x²} + C`. -/
theorem integral_dawkins (C a b : ℝ) :
    ∫ x in a..b, (5 * x - 3 * x ^ 5) * exp (x ^ 6 - 5 * x ^ 2) = dawkinsF C b - dawkinsF C a := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_dawkinsF C x) ?_
  apply Continuous.intervalIntegrable
  fun_prop
