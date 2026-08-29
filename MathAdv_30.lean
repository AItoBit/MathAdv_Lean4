import Mathlib

open scoped Real

/-- The function `f x = 1 / (sin x - cos x)`. -/
noncomputable def f (x : ℝ) : ℝ := 1 / (Real.sin x - Real.cos x)

/-- At any point where `sin x ≠ cos x`, `f` has derivative
`-(cos x + sin x) / (sin x - cos x)^2`. -/
theorem hasDerivAt_f (x : ℝ) (hx : Real.sin x - Real.cos x ≠ 0) :
    HasDerivAt f (-(Real.cos x + Real.sin x) / (Real.sin x - Real.cos x) ^ 2) x := by
  unfold f

  -- 1. Derivative of numerator (1 : ℝ)' = 0
  have h_num : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) x := hasDerivAt_const x (1 : ℝ)

  -- 2. Derivative of denominator: (sin x - cos x)' = cos x - (-sin x) = cos x + sin x
  have h_den : HasDerivAt (fun y => Real.sin y - Real.cos y) (Real.cos x + Real.sin x) x := by
    apply HasDerivAt.congr_deriv ((Real.hasDerivAt_sin x).sub (Real.hasDerivAt_cos x))
    ring

  -- 3. Apply the quotient rule: (u / v)' = (u'v - uv') / v²
  have h_div := h_num.div h_den hx
  apply HasDerivAt.congr_deriv h_div

  -- 4. Strip the division / denominator so `ring` only sees the numerator
  congr 1
  ring

/-- The derivative of `f x = 1 / (sin x - cos x)` is
`-(cos x + sin x) / (sin x - cos x)^2`, wherever `sin x ≠ cos x`. -/
theorem deriv_f (x : ℝ) (hx : Real.sin x - Real.cos x ≠ 0) :
    deriv f x = -(Real.cos x + Real.sin x) / (Real.sin x - Real.cos x) ^ 2 :=
  (hasDerivAt_f x hx).deriv
