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

set_option grind.warning false

open MeasureTheory intervalIntegral

/-- The comparison bound: on `(1, 4]` we have `1/√(x²-1) ≤ (x-1)^(-1/2)`. -/
lemma inv_sqrt_sq_sub_one_le (x : ℝ) (hx : 1 < x) :
    1 / Real.sqrt (x ^ 2 - 1) ≤ (x - 1) ^ (-(1 / 2) : ℝ) := by
  have hx1 : (0:ℝ) < x - 1 := by linarith
  have hle : x - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hs1 : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.mpr hx1
  have hmono : Real.sqrt (x - 1) ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_le_sqrt hle
  have hrw : (x - 1) ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt (x - 1) := by
    simp [Real.rpow_neg hx1.le, Real.sqrt_eq_rpow, one_div]
  rw [hrw]
  exact one_div_le_one_div_of_le hs1 hmono

/-- Integrability of `1/√(x²-1)` on `[1, 4]` (the integrand blows up at `x = 1`). -/
lemma intervalIntegrable_inv_sqrt_sq_sub_one :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x ^ 2 - 1)) volume 1 4 := by
  have hg : IntervalIntegrable (fun x : ℝ => (x - 1) ^ (-(1 / 2) : ℝ)) volume 1 4 := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume 0 3 :=
      intervalIntegrable_rpow' (by norm_num)
    have h1 := h0.comp_sub_right 1
    norm_num at h1
    exact h1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine MeasureTheory.Integrable.mono'
    (hg.1.mono_set (by intro x hx; exact hx)) ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop)).restrict
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : 1 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_sqrt_sq_sub_one_le x hx1

/-- `log (x + √(x²-1))` is an antiderivative of `1/√(x²-1)` for `x > 1`. -/
lemma hasDerivAt_log_add_sqrt (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t ^ 2 - 1)))
      (1 / Real.sqrt (x ^ 2 - 1)) x := by
  have hpos : (0:ℝ) < x ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).sub_const 1)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1))
      (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := hsq.sqrt (ne_of_gt hpos)
  have hsum : HasDerivAt (fun t : ℝ => t + Real.sqrt (t ^ 2 - 1))
      (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := (hasDerivAt_id x).add hsqrt
  have hne : x + Real.sqrt (x ^ 2 - 1) ≠ 0 := by positivity
  have := hsum.log hne
  convert this using 1
  field_simp
  ring

theorem strang_7_3_28 :
    ∫ x in (1 : ℝ)..(4 : ℝ), (1 / Real.sqrt (x ^ 2 - 1)) =
      Real.log (4 + Real.sqrt 15) := by
  have key := integral_eq_sub_of_hasDeriv_right_of_le (a := (1:ℝ)) (b := (4:ℝ))
    (f := fun t : ℝ => Real.log (t + Real.sqrt (t ^ 2 - 1)))
    (f' := fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1))
    (by norm_num)
    (by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht
        have : (1:ℝ) ≤ t := ht.1
        positivity)
    (fun t ht => (hasDerivAt_log_add_sqrt t ht.1).hasDerivWithinAt)
    intervalIntegrable_inv_sqrt_sq_sub_one
  rw [key]
  norm_num

#print axioms strang_7_3_28
