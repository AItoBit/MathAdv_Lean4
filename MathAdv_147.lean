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

open Real

/-- The arc-length of the catenary `γ(t) = (t, cosh t)` from `(0,1)` to `(a, cosh a)`
is `sinh a`. The positivity hypothesis `0 < a` is included as stated, though the
result holds for every real `a`. -/
theorem Pressley_1_2_1 (a : ℝ) (_ha : 0 < a) :
  let γ (t : ℝ) : ℝ × ℝ := (t, cosh t)
  ∫ t in (0 : ℝ)..a, sqrt ((deriv (fun x => (γ x).1) t) ^ 2 + (deriv (fun x => (γ x).2) t) ^ 2) = sinh a := by
  intro γ
  have hsimp : ∀ t : ℝ,
      sqrt ((deriv (fun x => (γ x).1) t) ^ 2 + (deriv (fun x => (γ x).2) t) ^ 2)
        = Real.cosh t := by
    intro t
    have h1 : deriv (fun x => (γ x).1) t = 1 := by
      simp [γ]
    have h2 : deriv (fun x => (γ x).2) t = Real.sinh t := by
      simp [γ]
    rw [h1, h2]
    have hsq : (1:ℝ) ^ 2 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq t]
    rw [hsq, Real.sqrt_sq (Real.cosh_pos t).le]
  simp only [hsimp]
  have hint : ∫ t in (0:ℝ)..a, Real.cosh t = Real.sinh a - Real.sinh 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sinh x)
      (Real.continuous_cosh.intervalIntegrable _ _)
  simpa using hint
