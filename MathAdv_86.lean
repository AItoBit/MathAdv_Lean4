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

open Complex Metric Set

/-- The contour integral `g(z) = ∮_C (s³ + 2s)/(s - z)³ ds`, where the contour `C` is the
positively oriented circle of center `c` and radius `R`. -/
noncomputable def g (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∮ s in C(c, R), (s ^ 3 + 2 * s) / (s - z) ^ 3

/-- Partial-fraction decomposition of the integrand around the pole `z`. -/
lemma integrand_decomp {s z : ℂ} (h : s ≠ z) :
    (s ^ 3 + 2 * s) / (s - z) ^ 3
      = (s - z) ^ (0 : ℤ) + 3 * z * (s - z) ^ (-1 : ℤ)
        + (3 * z ^ 2 + 2) * (s - z) ^ (-2 : ℤ) + (z ^ 3 + 2 * z) * (s - z) ^ (-3 : ℤ) := by
  have hsz : s - z ≠ 0 := sub_ne_zero.2 h
  field_simp
  ring

lemma circleIntegrable_zpow_sub (c z : ℂ) {R : ℝ} (hR : 0 ≤ R) (hz : z ∉ sphere c R) (n : ℤ) :
    CircleIntegrable (fun s => (s - z) ^ n) c R := by
  refine circleIntegrable_sub_zpow_iff.2 (Or.inr (Or.inr ?_))
  rwa [abs_of_nonneg hR]

lemma circleIntegrable_const_mul_zpow_sub (c z : ℂ) {R : ℝ} (hR : 0 ≤ R) (hz : z ∉ sphere c R)
    (n : ℤ) (a : ℂ) : CircleIntegrable (fun s => a * (s - z) ^ n) c R := by
  simpa [smul_eq_mul] using
    (circleIntegrable_zpow_sub c z hR hz n).const_fun_smul (a := a)

/-- The integral reduces to the residue term `3z ∮ (s - z)⁻¹ ds`. -/
lemma g_eq_three_mul (c z : ℂ) {R : ℝ} (hR : 0 ≤ R) (hz : z ∉ sphere c R) :
    g c R z = 3 * z * ∮ s in C(c, R), (s - z)⁻¹ := by
  have h0 := circleIntegrable_zpow_sub c z hR hz 0
  have h1 := circleIntegrable_const_mul_zpow_sub c z hR hz (-1) (3 * z)
  have h2 := circleIntegrable_const_mul_zpow_sub c z hR hz (-2) (3 * z ^ 2 + 2)
  have h3 := circleIntegrable_const_mul_zpow_sub c z hR hz (-3) (z ^ 3 + 2 * z)
  rw [g, circleIntegral.integral_congr hR (fun s hs => integrand_decomp (z := z)
    (by rintro rfl; exact hz hs))]
  rw [circleIntegral.integral_add
      (f := fun s => (s - z) ^ (0 : ℤ) + 3 * z * (s - z) ^ (-1 : ℤ)
        + (3 * z ^ 2 + 2) * (s - z) ^ (-2 : ℤ))
      (g := fun s => (z ^ 3 + 2 * z) * (s - z) ^ (-3 : ℤ)) ((h0.add h1).add h2) h3,
    circleIntegral.integral_add
      (f := fun s => (s - z) ^ (0 : ℤ) + 3 * z * (s - z) ^ (-1 : ℤ))
      (g := fun s => (3 * z ^ 2 + 2) * (s - z) ^ (-2 : ℤ)) (h0.add h1) h2,
    circleIntegral.integral_add (f := fun s => (s - z) ^ (0 : ℤ))
      (g := fun s => 3 * z * (s - z) ^ (-1 : ℤ)) h0 h1,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_zpow_of_ne (by decide) c z R,
    circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) c z R,
    circleIntegral.integral_sub_zpow_of_ne (by decide : (-3 : ℤ) ≠ -1) c z R]
  simp

/-- **Inside the contour**: if `z` lies inside the circle `C(c, R)` then `g(z) = 6πi z`. -/
theorem g_inside (c z : ℂ) {R : ℝ} (hz : z ∈ ball c R) :
    g c R z = 6 * Real.pi * Complex.I * z := by
  have hR : 0 ≤ R := (dist_nonneg.trans_lt hz).le
  have hzs : z ∉ sphere c R := by
    simp only [mem_sphere_iff_norm, Metric.mem_ball, dist_eq_norm] at hz ⊢
    exact ne_of_lt hz
  rw [g_eq_three_mul c z hR hzs, circleIntegral.integral_sub_inv_of_mem_ball hz]
  ring

/-- **Outside the contour**: if `z` lies outside the closed disc bounded by `C(c, R)` then
`g(z) = 0`. -/
theorem g_outside (c z : ℂ) {R : ℝ} (hR : 0 ≤ R) (hz : z ∉ closedBall c R) :
    g c R z = 0 := by
  have hne : ∀ s ∈ closedBall c R, s - z ≠ 0 := by
    intro s hs hsz
    have hsz' : s = z := sub_eq_zero.1 hsz
    exact hz (hsz' ▸ hs)
  have hzs : z ∉ sphere c R := fun h => hz (sphere_subset_closedBall h)
  have hzero : (∮ s in C(c, R), (s - z)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty ?_ ?_
    · exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) hne
    · intro s hs
      exact (differentiableAt_id.sub_const z).inv (hne s (ball_subset_closedBall hs.1))
  rw [g_eq_three_mul c z hR hzs, hzero, mul_zero]
