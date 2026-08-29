import Mathlib

/-- The derivative of `f x = (1 + 2x + 3x²)(5x + 8x² - x³)` is
`5 + 36x + 90x² + 88x³ - 15x⁴`. -/
theorem dawkins_3_4_3 :
    deriv (fun x : ℝ => (1 + 2*x + 3*x^2) * (5*x + 8*x^2 - x^3)) =
      fun x => 5 + 36*x + 90*x^2 + 88*x^3 - 15*x^4 := by
  funext x
  have h : (fun x : ℝ => (1 + 2*x + 3*x^2) * (5*x + 8*x^2 - x^3))
      = fun x : ℝ => 5*x + 18*x^2 + 30*x^3 + 22*x^4 - 3*x^5 := by
    funext x; ring
  rw [h]
  have h1 : HasDerivAt (fun x : ℝ => 5*x + 18*x^2 + 30*x^3 + 22*x^4 - 3*x^5)
      (5 + 36*x + 90*x^2 + 88*x^3 - 15*x^4) x := by
    have := (((hasDerivAt_id x).const_mul (5:ℝ)).add
      (((hasDerivAt_pow 2 x)).const_mul (18:ℝ))).add
      (((hasDerivAt_pow 3 x)).const_mul (30:ℝ))
    have h2 := (this.add ((hasDerivAt_pow 4 x).const_mul (22:ℝ))).sub
      ((hasDerivAt_pow 5 x).const_mul (3:ℝ))
    convert h2 using 1
    push_cast
    ring
  exact h1.deriv
