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
# Two thick slabs of rock in contact

One very thick layer of rock at `100°C` is placed upon another of the same material at
`0°C`.  Since both bodies are very thick, the relevant model is that of *temperatures in
an infinite bar*, whose solution is the error-function profile

`u(x,t) = 50 + 50 · erf (x / (2√(k t)))`,

`x` being the signed distance to the plane of contact.

With `k = 0.01` c.g.s. and `t = 100 hr = 360000 s` we have `2√(k t) = 120`, so the points
`x = ±60` cm correspond to the argument `±1/2` of `erf`, and the temperatures there are
`50 ± 50·erf(1/2) ≈ 76°C` and `≈ 24°C`.
-/

/-- The error function `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) *
    ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- Temperature in an infinite bar made of two half-infinite bars initially at `100°C`
(for `x > 0`) and `0°C` (for `x < 0`), with diffusivity `k`. -/
noncomputable def heatSolution (k : ℝ) (t x : ℝ) : ℝ :=
  50 + 50 * erf (x / (2 * Real.sqrt (k * t)))

namespace HeatSlab

/-- Elementary lower bound `1 - t² ≤ e^{-t²}`. -/
lemma exp_neg_sq_lower (t : ℝ) : 1 - t ^ 2 ≤ Real.exp (-t ^ 2) := by
  have := Real.add_one_le_exp (-t ^ 2)
  linarith

/-- Elementary upper bound `e^{-t²} ≤ 1 - t² + t⁴/2`. -/
lemma exp_neg_sq_upper (t : ℝ) : Real.exp (-t ^ 2) ≤ 1 - t ^ 2 + t ^ 4 / 2 := by
  set s := t ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg t
  have h1 : 1 + s + s ^ 2 / 2 ≤ Real.exp s := Real.quadratic_le_exp_of_nonneg hs0
  have hpos : (0 : ℝ) < 1 + s + s ^ 2 / 2 := by nlinarith
  have h2 : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
  have h3 : (Real.exp s)⁻¹ ≤ (1 + s + s ^ 2 / 2)⁻¹ := inv_anti₀ hpos h1
  have h4 : (1 + s + s ^ 2 / 2)⁻¹ ≤ 1 - s + s ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [sq_nonneg s, sq_nonneg (s * s)]
  have ht4 : t ^ 4 = s ^ 2 := by rw [hs]; ring
  rw [ht4, h2]
  linarith

private lemma integrable_exp_neg_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t ^ 2)) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

private lemma integrable_poly_lower (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => 1 - t ^ 2) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

private lemma integrable_poly_upper (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => 1 - t ^ 2 + t ^ 4 / 2) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Two-sided numerical bounds for `∫₀^{1/2} e^{-t²} dt`. -/
lemma integral_half_bounds :
    (11 / 24 : ℝ) ≤ (∫ t in (0 : ℝ)..(1 / 2), Real.exp (-t ^ 2)) ∧
      (∫ t in (0 : ℝ)..(1 / 2), Real.exp (-t ^ 2)) ≤ 443 / 960 := by
  constructor
  · have h : (∫ t in (0 : ℝ)..(1 / 2), (1 - t ^ 2)) ≤
        ∫ t in (0 : ℝ)..(1 / 2), Real.exp (-t ^ 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (integrable_poly_lower _ _) (integrable_exp_neg_sq _ _)
      intro x _
      exact exp_neg_sq_lower x
    have hc : (∫ t in (0 : ℝ)..(1 / 2), (1 - t ^ 2)) = 11 / 24 := by
      norm_num [intervalIntegral.integral_sub, integral_pow,
        intervalIntegral.intervalIntegrable_pow]
    linarith [hc ▸ h]
  · have h : (∫ t in (0 : ℝ)..(1 / 2), Real.exp (-t ^ 2)) ≤
        ∫ t in (0 : ℝ)..(1 / 2), (1 - t ^ 2 + t ^ 4 / 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (integrable_exp_neg_sq _ _) (integrable_poly_upper _ _)
      intro x _
      exact exp_neg_sq_upper x
    have hc : (∫ t in (0 : ℝ)..(1 / 2), (1 - t ^ 2 + t ^ 4 / 2)) = 443 / 960 := by
      norm_num [intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_div, integral_pow,
        intervalIntegral.intervalIntegrable_pow]
    linarith [hc ▸ h]

/-- Two-sided numerical bounds for `∫_{-1/2}^0 e^{-t²} dt`. -/
lemma integral_neg_half_bounds :
    (11 / 24 : ℝ) ≤ (∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2)) ∧
      (∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2)) ≤ 443 / 960 := by
  constructor
  · have h : (∫ t in (-(1 / 2) : ℝ)..0, (1 - t ^ 2)) ≤
        ∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (integrable_poly_lower _ _) (integrable_exp_neg_sq _ _)
      intro x _
      exact exp_neg_sq_lower x
    have hc : (∫ t in (-(1 / 2) : ℝ)..0, (1 - t ^ 2)) = 11 / 24 := by
      norm_num [intervalIntegral.integral_sub, integral_pow,
        intervalIntegral.intervalIntegrable_pow]
    linarith [hc ▸ h]
  · have h : (∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2)) ≤
        ∫ t in (-(1 / 2) : ℝ)..0, (1 - t ^ 2 + t ^ 4 / 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (integrable_exp_neg_sq _ _) (integrable_poly_upper _ _)
      intro x _
      exact exp_neg_sq_upper x
    have hc : (∫ t in (-(1 / 2) : ℝ)..0, (1 - t ^ 2 + t ^ 4 / 2)) = 443 / 960 := by
      norm_num [intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_div, integral_pow,
        intervalIntegral.intervalIntegrable_pow]
    linarith [hc ▸ h]

lemma sqrt_pi_lt : Real.sqrt Real.pi < 1.7725 := by
  rw [show (1.7725 : ℝ) = Real.sqrt (1.7725 ^ 2) by rw [Real.sqrt_sq] ; norm_num]
  apply Real.sqrt_lt_sqrt Real.pi_pos.le
  nlinarith [Real.pi_lt_d4]

lemma sqrt_pi_gt : (1.7724 : ℝ) < Real.sqrt Real.pi := by
  rw [show (1.7724 : ℝ) = Real.sqrt (1.7724 ^ 2) by rw [Real.sqrt_sq] ; norm_num]
  apply Real.sqrt_lt_sqrt (by norm_num)
  nlinarith [Real.pi_gt_d6]

/-- `erf (1/2) ≈ 0.5205`, to within the accuracy needed here. -/
lemma erf_half_bounds : (0.51 : ℝ) ≤ erf (1 / 2) ∧ erf (1 / 2) ≤ 0.53 := by
  obtain ⟨hI1, hI2⟩ := integral_half_bounds
  have hsp0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlt := sqrt_pi_lt
  have hgt := sqrt_pi_gt
  have key : erf (1 / 2) =
      (2 * ∫ t in (0 : ℝ)..(1 / 2), Real.exp (-t ^ 2)) / Real.sqrt Real.pi := by
    unfold erf; field_simp
  rw [key]
  constructor
  · rw [le_div_iff₀ hsp0]; nlinarith
  · rw [div_le_iff₀ hsp0]; nlinarith

/-- `erf (-1/2) ≈ -0.5205`, to within the accuracy needed here. -/
lemma erf_neg_half_bounds : (-0.53 : ℝ) ≤ erf (-(1 / 2)) ∧ erf (-(1 / 2)) ≤ -0.51 := by
  obtain ⟨hI1, hI2⟩ := integral_neg_half_bounds
  have hsp0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlt := sqrt_pi_lt
  have hgt := sqrt_pi_gt
  have hsymm : (∫ t in (0 : ℝ)..(-(1 / 2) : ℝ), Real.exp (-t ^ 2)) =
      -∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2) := intervalIntegral.integral_symm _ _
  have key : erf (-(1 / 2)) =
      (-(2 * ∫ t in (-(1 / 2) : ℝ)..0, Real.exp (-t ^ 2))) / Real.sqrt Real.pi := by
    unfold erf
    rw [hsymm]
    field_simp
  rw [key]
  constructor
  · rw [le_div_iff₀ hsp0]; nlinarith
  · rw [div_le_iff₀ hsp0]; nlinarith

end HeatSlab

/-- **Two thick rock layers.**  With `k = 0.01` c.g.s., `100` hours after contact the
temperatures `60` cm on either side of the plane of contact are `76°C` and `24°C` to the
nearest degree. -/
theorem brown_3 :
    let k : ℝ := 0.01
    let t_hours : ℝ := 100
    let t : ℝ := t_hours * 3600
    let u : ℝ → ℝ → ℝ := heatSolution k
    |u t 60 - 76| ≤ (0.5 : ℝ) ∧
    |u t (-60) - 24| ≤ (0.5 : ℝ) := by
  intro k t_hours t u
  have hsq : Real.sqrt (k * t) = 60 := by
    show Real.sqrt (0.01 * (100 * 3600) : ℝ) = 60
    rw [show (0.01 * (100 * 3600) : ℝ) = 60 ^ 2 by norm_num, Real.sqrt_sq] ; norm_num
  have h1 : u t 60 = 50 + 50 * erf (1 / 2) := by
    show heatSolution k t 60 = _
    unfold heatSolution
    rw [hsq]
    norm_num
  have h2 : u t (-60) = 50 + 50 * erf (-(1 / 2)) := by
    show heatSolution k t (-60) = _
    unfold heatSolution
    rw [hsq]
    norm_num
  obtain ⟨ha1, ha2⟩ := HeatSlab.erf_half_bounds
  obtain ⟨hb1, hb2⟩ := HeatSlab.erf_neg_half_bounds
  rw [h1, h2]
  constructor
  · rw [abs_le]; constructor <;> norm_num <;> linarith
  · rw [abs_le]; constructor <;> norm_num <;> linarith
