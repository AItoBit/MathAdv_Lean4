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

open Filter Topology

/-- **Derivative of `f(x) = x³ · ln(x⁵)`.**
As a function on all of `ℝ`, `deriv f x = 3x² ln(x⁵) + 5x²`.
(Recall Lean's `Real.log` satisfies `log y = log |y|` and `log 0 = 0`, so the
identity also holds at `x = 0` and for negative `x`.) -/
theorem dawkins_3_9_18 :
  deriv (fun x : ℝ => x^3 * Real.log (x ^ 5)) =
    fun x => 3 * x ^ 2 * Real.log (x ^ 5) + 5 * x ^ 2 := by
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · -- At `x = 0` the difference quotient is `5 h² log |h| → 0`.
    have hslope : Tendsto (slope (fun x : ℝ => x^3 * Real.log (x ^ 5)) 0) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have hpos : Tendsto (fun t : ℝ => Real.log t * t^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        refine (tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by norm_num)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t _
        rw [Real.rpow_two]
      have hcomp : Tendsto (fun h : ℝ => Real.log |h| * |h|^2) (𝓝[≠] (0:ℝ)) (𝓝 0) :=
        hpos.comp tendsto_abs_nhdsNE_zero
      have h5 : Tendsto (fun h : ℝ => Real.log |h| * |h|^2 * 5) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
        simpa using hcomp.mul_const (5:ℝ)
      refine h5.congr ?_
      intro h
      by_cases h0 : h = 0
      · simp [h0, slope]
      · rw [slope_def_field, Real.log_abs, sq_abs, Real.log_pow, sub_zero, eq_div_iff h0]
        push_cast
        ring
    have hd : HasDerivAt (fun x : ℝ => x^3 * Real.log (x ^ 5)) 0 0 :=
      hasDerivAt_iff_tendsto_slope.2 hslope
    rw [hd.deriv]
    norm_num
  · -- Away from `0`: product rule together with the chain rule for `log`.
    have h1 : HasDerivAt (fun x : ℝ => x^5) (5 * x^4) x := by
      simpa using (hasDerivAt_pow 5 x)
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x^5)) ((x^5)⁻¹ * (5 * x^4)) x :=
      (Real.hasDerivAt_log (by positivity)).comp x h1
    have h3 : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
      simpa using (hasDerivAt_pow 3 x)
    have h4 : HasDerivAt (fun x : ℝ => x^3 * Real.log (x^5))
        (3 * x^2 * Real.log (x^5) + x^3 * ((x^5)⁻¹ * (5 * x^4))) x := h3.mul h2
    rw [h4.deriv]
    field_simp
