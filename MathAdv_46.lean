import Mathlib

open Complex

/-- For a real `x`, `cos (i x) = cosh x` and `sin (i x) = i sinh x`
(as identities between complex numbers). -/
theorem strang_9_4_34
  (x : ℝ) :
  cos (I * x) = cosh x ∧ sin (I * x) = I * sinh x := by
  constructor
  · rw [mul_comm, Complex.cos_mul_I]
  · rw [mul_comm, Complex.sin_mul_I, mul_comm]
