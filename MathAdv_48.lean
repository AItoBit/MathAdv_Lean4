import Mathlib

open Real

/-- Partial derivatives of `f (x, y) = log (x + 2y)`.

The hypothesis `x + 2 * y ≠ 0` is needed: `log` is not differentiable at `0`
(the original informal statement implicitly assumes the argument of `log` is
positive, which is a special case of this hypothesis). -/
theorem strang_13_2_8 (x y : ℝ) (h : x + 2 * y ≠ 0) :
    (HasDerivAt (fun x0 => log (x0 + 2 * y)) (1 / (x + 2 * y)) x) ∧
    (HasDerivAt (fun y0 => log (x + 2 * y0)) (2 / (x + 2 * y)) y) := by
  constructor
  · have hin : HasDerivAt (fun x0 : ℝ => x0 + 2 * y) 1 x := by
      apply HasDerivAt.congr_deriv ((hasDerivAt_id x).add_const (2 * y))
      ring
    apply HasDerivAt.congr_deriv (hin.log h)
    simp only [one_div]
  · have hin : HasDerivAt (fun y0 : ℝ => x + 2 * y0) 2 y := by
      apply HasDerivAt.congr_deriv (((hasDerivAt_id y).const_mul (2 : ℝ)).const_add x)
      ring
    apply HasDerivAt.congr_deriv (hin.log h)
    simp only [div_eq_inv_mul, mul_comm]
