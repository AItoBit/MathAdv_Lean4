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
# A vibrating string with damping proportional to velocity

The physical problem: a stretched string of (constant) linear mass density `rho > 0` under
(constant) tension `T`, subject in addition to a damping force per unit length proportional to
the transverse velocity, with damping constant `delta`.

For small transverse displacements `y t x`, the net transverse force per unit length exerted by
the tension is `T * ∂²y/∂x²`, and the damping contributes `- delta * ∂y/∂t`.  Newton's second law
per unit length therefore reads

  `rho * ∂²y/∂t² = T * ∂²y/∂x² - delta * ∂y/∂t`.

Dividing by `rho` and setting `a = sqrt (T / rho)`, `b = delta / rho` gives the stated equation of
motion

  `∂²y/∂t² = a² ∂²y/∂x² - b ∂y/∂t`,

which is the equation of the *vibrating string* (answer (c)), with a damping term added.

The original statement of the exercise as a bare Lean formula,

```
theorem brown_2 {a b : ℝ} {y : ℝ → ℝ → ℝ} :
    ∀ (t x : ℝ),
    deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
      a ^ 2 * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
      - b * deriv (fun t0 => y t0 x) t := by
  sorry
```

is **false**: it asserts the equation for *arbitrary* `a`, `b` and *arbitrary* `y`, with no physical
hypothesis relating them.  This is recorded below as `brown_2_as_stated_false`, and the intended
content of the exercise is formalized as `damped_string_equation_of_motion`.
-/

/-- The equation of motion of a string with damping proportional to the velocity.

Hypothesis `hNewton` is Newton's second law applied to an element of the string: mass per unit
length `rho` times the transverse acceleration equals the transverse force per unit length coming
from the tension, `T * ∂²y/∂x²`, minus the damping force per unit length, `delta * ∂y/∂t`.

Setting `a = Real.sqrt (T / rho)` and `b = delta / rho`, this takes the form
`∂²y/∂t² = a² ∂²y/∂x² - b ∂y/∂t`. -/
theorem damped_string_equation_of_motion
    {rho T delta a b : ℝ} {y : ℝ → ℝ → ℝ}
    (hrho : 0 < rho) (hT : 0 ≤ T)
    (hNewton : ∀ t x : ℝ,
      rho * deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
        T * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
        - delta * deriv (fun t0 => y t0 x) t)
    (ha : a = Real.sqrt (T / rho)) (hb : b = delta / rho) :
    ∀ t x : ℝ,
      deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
        a ^ 2 * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
        - b * deriv (fun t0 => y t0 x) t := by
  have hsq : a ^ 2 = T / rho := by
    rw [ha, Real.sq_sqrt (div_nonneg hT hrho.le)]
  intro t x
  have h := hNewton t x
  rw [hsq, hb]
  field_simp
  linarith [h]

/-- The exercise's equation cannot hold for arbitrary coefficients and arbitrary displacement:
for `y t x = t`, `a = 0` and `b = 1` the two sides differ. -/
theorem brown_2_as_stated_false :
    ¬ (∀ (a b : ℝ) (y : ℝ → ℝ → ℝ) (t x : ℝ),
        deriv (fun t0 => deriv (fun t1 => y t1 x) t0) t =
          a ^ 2 * deriv (fun x0 => deriv (fun x1 => y t x1) x0) x
          - b * deriv (fun t0 => y t0 x) t) := by
  intro h
  have := h 0 1 (fun t _ => t) 0 0
  simp at this
