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
# Residue at `0` of `sinh z / (z ^ 4 (1 - z ^ 2))`

We define the residue of a function `f : ℂ → ℂ` at a point `c` as the limit, as the radius
`r` tends to `0` from above, of `(2 π i)⁻¹ ∮_{|z - c| = r} f z`, and we show that the residue
at `0` of `z ↦ sinh z / (z ^ 4 (1 - z ^ 2))` equals `7 / 6`.

The computation follows the "series multiplication" argument: on the punctured unit disc
`sinh z / (z ^ 4 (1 - z ^ 2)) = sinh z / z ^ 4 + sinh z / z ^ 2 + sinh z / (1 - z ^ 2)`,
where the first two terms contribute `1 / 6` and `1` (via Cauchy's formula for derivatives)
and the last term, being holomorphic, contributes `0`.

Note that Mathlib has no `residue` operator, so the notion is defined here from scratch.
-/

namespace ResidueSinh

open Complex Metric Filter Topology

/-- The residue of `f` at `c`: the limit as `r → 0⁺` of `(2 π i)⁻¹ ∮_{|z - c| = r} f z`. -/
noncomputable def residue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r : ℝ =>
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f z

/-- Cauchy's integral formula for the third derivative: `∮ sinh z / z ^ 4 = 2 π i / 6`. -/
theorem circleIntegral_sinh_div_pow_four (r : ℝ) (hr : 0 < r) :
    (∮ z in C((0 : ℂ), r), Complex.sinh z / z ^ 4) = 2 * Real.pi * Complex.I * (1 / 6) := by
  have hd : DifferentiableOn ℂ Complex.sinh (Metric.closedBall (0 : ℂ) r) :=
    Complex.differentiable_sinh.differentiableOn
  have h := hd.circleIntegral_one_div_sub_center_pow_smul hr 3
  simp only [sub_zero, smul_eq_mul, one_div] at h
  have h3 : iteratedDeriv 3 Complex.sinh 0 = 1 := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero, Complex.deriv_sinh, Complex.deriv_cosh]
  rw [h3] at h
  rw [show (fun z : ℂ => Complex.sinh z / z ^ 4) = fun z : ℂ => (z ^ (3 + 1))⁻¹ * Complex.sinh z by
    funext z; rw [div_eq_inv_mul]]
  rw [h]
  norm_num
  ring

/-- Cauchy's integral formula for the first derivative: `∮ sinh z / z ^ 2 = 2 π i`. -/
theorem circleIntegral_sinh_div_sq (r : ℝ) (hr : 0 < r) :
    (∮ z in C((0 : ℂ), r), Complex.sinh z / z ^ 2) = 2 * Real.pi * Complex.I := by
  have hd : DifferentiableOn ℂ Complex.sinh (Metric.closedBall (0 : ℂ) r) :=
    Complex.differentiable_sinh.differentiableOn
  have h := hd.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [sub_zero, smul_eq_mul, one_div] at h
  have h1 : iteratedDeriv 1 Complex.sinh 0 = 1 := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero, Complex.deriv_sinh]
  rw [h1] at h
  rw [show (fun z : ℂ => Complex.sinh z / z ^ 2) = fun z : ℂ => (z ^ (1 + 1))⁻¹ * Complex.sinh z by
    funext z; rw [div_eq_inv_mul]]
  rw [h]
  norm_num

theorem differentiableAt_sinh_div_one_sub_sq {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.sinh w / (1 - w ^ 2)) z := by
  have hne : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have h1 : z ^ 2 = 1 := by linear_combination -h
    have h2 : ‖z‖ ^ 2 = 1 := by
      have := congrArg (‖·‖) h1
      simpa [norm_pow] using this
    nlinarith [norm_nonneg z]
  exact (Complex.differentiable_sinh z).div (by fun_prop) hne

/-- The holomorphic part contributes nothing: `∮ sinh z / (1 - z ^ 2) = 0` for `r < 1`. -/
theorem circleIntegral_sinh_div_one_sub_sq (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (∮ z in C((0 : ℂ), r), Complex.sinh z / (1 - z ^ 2)) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty ?_ ?_
  · intro z hz
    have : ‖z‖ < 1 := lt_of_le_of_lt (by simpa [Complex.dist_eq] using hz) hr1
    exact ((differentiableAt_sinh_div_one_sub_sq this).continuousAt).continuousWithinAt
  · intro z hz
    have : ‖z‖ < 1 :=
      lt_trans (by simpa [Complex.dist_eq] using (mem_ball_zero_iff.mp hz.1)) hr1
    exact differentiableAt_sinh_div_one_sub_sq this

/-- The contour integral of `sinh z / (z ^ 4 (1 - z ^ 2))` over a circle of radius `0 < r < 1`
centred at the origin equals `2 π i * (7 / 6)`. -/
theorem circleIntegral_eq (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (∮ z in C((0 : ℂ), r), Complex.sinh z / (z ^ 4 * (1 - z ^ 2)))
      = 2 * Real.pi * Complex.I * (7 / 6) := by
  have hzne : ∀ z ∈ Metric.sphere (0 : ℂ) r, z ≠ 0 ∧ (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    refine ⟨hz0, ?_⟩
    intro h
    have h1 : z ^ 2 = 1 := by linear_combination -h
    have h2 : ‖z‖ ^ 2 = 1 := by
      have := congrArg (‖·‖) h1
      simpa [norm_pow] using this
    rw [hz] at h2
    nlinarith
  have hcong : Set.EqOn (fun z : ℂ => Complex.sinh z / (z ^ 4 * (1 - z ^ 2)))
      (fun z : ℂ => (Complex.sinh z / z ^ 4 + Complex.sinh z / z ^ 2)
        + Complex.sinh z / (1 - z ^ 2)) (Metric.sphere (0 : ℂ) r) := by
    intro z hz
    obtain ⟨hz0, hne⟩ := hzne z hz
    simp only
    field_simp
    ring
  have hc1 : CircleIntegrable (fun z : ℂ => Complex.sinh z / z ^ 4) 0 r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    have h : ContinuousAt (fun w : ℂ => Complex.sinh w / w ^ 4) z :=
      Complex.continuous_sinh.continuousAt.div (continuous_pow 4).continuousAt
        (pow_ne_zero _ (hzne z hz).1)
    exact h.continuousWithinAt
  have hc2 : CircleIntegrable (fun z : ℂ => Complex.sinh z / z ^ 2) 0 r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    have h : ContinuousAt (fun w : ℂ => Complex.sinh w / w ^ 2) z :=
      Complex.continuous_sinh.continuousAt.div (continuous_pow 2).continuousAt
        (pow_ne_zero _ (hzne z hz).1)
    exact h.continuousWithinAt
  have hc3 : CircleIntegrable (fun z : ℂ => Complex.sinh z / (1 - z ^ 2)) 0 r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    have hz1 : ‖z‖ < 1 := by
      rw [mem_sphere_zero_iff_norm] at hz; rw [hz]; exact hr1
    exact (differentiableAt_sinh_div_one_sub_sq hz1).continuousAt.continuousWithinAt
  have hadd1 := circleIntegral.integral_add (hc1.add hc2) hc3
  have hadd2 := circleIntegral.integral_add hc1 hc2
  simp only [Pi.add_apply] at hadd1
  rw [circleIntegral.integral_congr hr.le hcong, hadd1, hadd2,
    circleIntegral_sinh_div_pow_four r hr, circleIntegral_sinh_div_sq r hr,
    circleIntegral_sinh_div_one_sub_sq r hr hr1]
  ring

/-- **The residue at `z = 0` of `sinh z / (z ^ 4 (1 - z ^ 2))` is `7 / 6`.** -/
theorem residue_sinh_div_pow_four_mul_one_sub_sq :
    residue (fun z : ℂ => Complex.sinh z / (z ^ 4 * (1 - z ^ 2))) 0 = 7 / 6 := by
  have h : (fun _ : ℝ => (7 : ℂ) / 6) =ᶠ[𝓝[>] (0 : ℝ)] fun r : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ z in C((0 : ℂ), r), Complex.sinh z / (z ^ 4 * (1 - z ^ 2)) := by
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with r hr
    rw [circleIntegral_eq r hr.1 hr.2]
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    field_simp
  exact (Filter.Tendsto.congr' h tendsto_const_nhds).limUnder_eq

end ResidueSinh
