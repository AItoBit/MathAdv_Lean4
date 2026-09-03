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

/-!
# Damped vibrating string

A string with linear mass density `rho > 0` under tension `T`, subject in addition to a
damping (air-resistance) force proportional to the transverse velocity with constant of
proportionality `k` per unit length, obeys Newton's second law in the form

  `rho * ∂²y/∂t² = T * ∂²y/∂x² - k * ∂y/∂t`.

Dividing by `rho` and setting `a² = T / rho`, `b = k / rho` puts the equation of motion in
the stated form

  `∂²y/∂t² = a² ∂²y/∂x² - b ∂y/∂t`,

which is the equation of the vibrating string (with a damping term) — answer (c).

The original statement of the exercise, as literally quantified over *all* functions `y`
and *all* constants `a`, `b`, is of course false; this is recorded below as
`brown_2_unconditional_false`, together with the corrected, conditional statement
`brown_2`.
-/

/-- **The equation of motion of a damped vibrating string.**

If Newton's second law for the string reads
`rho * ∂²y/∂t² = T * ∂²y/∂x² - k * ∂y/∂t` (with linear density `rho > 0`, tension `T`
and damping constant `k`), and if `a` and `b` are defined by `a ^ 2 = T / rho` and
`b = k / rho`, then the motion satisfies
`∂²y/∂t² = a ^ 2 * ∂²y/∂x² - b * ∂y/∂t`. -/
theorem brown_2 {a b rho T k : ℝ} {y : ℝ → ℝ → ℝ} (hrho : rho ≠ 0)
    (ha : a ^ 2 = T / rho) (hb : b = k / rho)
    (hNewton : ∀ (t x : ℝ),
      rho * deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
        T * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
        - k * deriv (fun t0 => y t0 x) t) :
    ∀ (t x : ℝ),
    deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
      a ^ 2 * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
      - b * deriv (fun t0 => y t0 x) t := by
  intro t x
  have h := hNewton t x
  rw [ha, hb]
  field_simp
  linarith [h]

/-- The exercise's equation is *not* an identity valid for arbitrary displacement functions
`y` and arbitrary constants `a`, `b`: it expresses a physical law (Newton's second law for
the string).  Here is an explicit counterexample: `y t x = t ^ 2` with `a = b = 0`. -/
theorem brown_2_unconditional_false :
    ¬ (∀ (a b : ℝ) (y : ℝ → ℝ → ℝ) (t x : ℝ),
        deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
          a ^ 2 * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
          - b * deriv (fun t0 => y t0 x) t) := by
  intro h
  have := h 0 0 (fun t _ => t ^ 2) 0 0
  have e1 : (fun (t0 : ℝ) => deriv (fun (t1 : ℝ) => t1 ^ 2) t0) = fun t0 : ℝ => 2 * t0 := by
    funext t0
    simp
  rw [e1] at this
  simp only [zero_mul] at this
  rw [deriv_const_mul_field] at this
  simp at this
