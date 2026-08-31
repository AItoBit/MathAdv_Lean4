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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- The angle between `u = (m+1, -m+2, -3)` and `v = (-3, m+1, -m+2)` is always
`120° = 2π/3`, for every real `m`. -/
theorem question_5 :
  ∀ m : ℝ,
    let u : ℝ × ℝ × ℝ := (m + 1, (-m + 2, -3))
    let v : ℝ × ℝ × ℝ := (-3, (m + 1, -m + 2))
    (Real.arccos
        ((u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2) /
         (Real.sqrt (u.1^2 + u.2.1^2 + u.2.2^2) *
          Real.sqrt (v.1^2 + v.2.1^2 + v.2.2^2))))
      = (2 * Real.pi / 3) := by
  intro m
  simp only
  have hA : (0:ℝ) < (m+1)^2 + (-m+2)^2 + (-3:ℝ)^2 := by positivity
  have hs : Real.sqrt ((m+1)^2 + (-m+2)^2 + (-3:ℝ)^2) *
      Real.sqrt ((-3:ℝ)^2 + (m+1)^2 + (-m+2)^2) = (m+1)^2 + (-m+2)^2 + 9 := by
    rw [show ((-3:ℝ)^2 + (m+1)^2 + (-m+2)^2) = (m+1)^2 + (-m+2)^2 + (-3:ℝ)^2 by ring,
      Real.mul_self_sqrt hA.le]
    ring
  rw [hs]
  have key : ((m+1) * (-3) + (-m+2) * (m+1) + (-3) * (-m+2)) / ((m+1)^2 + (-m+2)^2 + 9)
      = -(1/2) := by
    rw [div_eq_iff (by nlinarith [sq_nonneg (m+1), sq_nonneg (-m+2)])]
    ring
  rw [key]
  have hc : Real.cos (2 * Real.pi / 3) = -(1/2) := by
    have h : (2 * Real.pi / 3) = Real.pi - Real.pi/3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [← hc, Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])]
