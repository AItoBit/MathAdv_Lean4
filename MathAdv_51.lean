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

open MeasureTheory Set

namespace Strang

/-- The closed unit disk in the plane. -/
def unitDisk : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

lemma measurableSet_unitDisk : MeasurableSet unitDisk := by
  have : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  exact measurableSet_le this.measurable measurable_const

/-- Squared radius under the polar parametrization. -/
lemma sq_add_sq_polar (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

/-- On the box `(0,1] × (-π, π)` the polar integrand is `r ^ 3`. -/
lemma polar_integrand_on_box (p : ℝ × ℝ) (hp : p ∈ Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π) :
    p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p)
      = p.1 ^ 3 := by
  obtain ⟨hr, -⟩ := hp
  simp only [mem_Ioc] at hr
  have hmem : polarCoord.symm p ∈ unitDisk := by
    simp only [unitDisk, mem_ofPred, polarCoord_symm_apply, sq_add_sq_polar]
    nlinarith [hr.1, hr.2]
  rw [Set.indicator_of_mem hmem]
  simp only [polarCoord_symm_apply, sq_add_sq_polar, smul_eq_mul]
  ring

/-- Outside the box, the polar integrand vanishes. -/
lemma polar_integrand_off_box (p : ℝ × ℝ)
    (hp : p ∈ (Ioi (0:ℝ) ×ˢ Ioo (-π) π) \ (Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π)) :
    p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p) = 0 := by
  obtain ⟨⟨hr, hθ⟩, hnot⟩ := hp
  simp only [mem_Ioi] at hr
  have hr1 : 1 < p.1 := by
    by_contra h
    exact hnot ⟨mem_Ioc.2 ⟨hr, not_lt.1 h⟩, hθ⟩
  have hnotmem : polarCoord.symm p ∉ unitDisk := by
    simp only [unitDisk, mem_ofPred, polarCoord_symm_apply, sq_add_sq_polar, not_le]
    nlinarith
  rw [Set.indicator_of_notMem hnotmem, smul_zero]

lemma integrableOn_box : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3)
    (Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π) volume := by
  apply Measure.integrableOn_of_bounded (M := 1)
  · have : (volume (Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π)) =
        volume (Ioc (0:ℝ) 1) * volume (Ioo (-π) π) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    rw [this]
    simp [Real.volume_Ioc, Real.volume_Ioo]
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem
      ((measurableSet_Ioc).prod (measurableSet_Ioo))] with p hp
    obtain ⟨hr, -⟩ := hp
    simp only [mem_Ioc] at hr
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.1.le 3)]
    exact pow_le_one₀ hr.1.le hr.2

lemma integral_box : ∫ p in Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π, p.1 ^ 3 = π / 2 := by
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact integrableOn_box)]
  have hinner : ∀ r : ℝ, (∫ _ in Ioo (-π) π, r ^ 3) = (2 * π) * r ^ 3 := by
    intro r
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg]),
      smul_eq_mul]
    ring
  simp only [hinner]
  rw [integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem volume_under_paraboloid_over_unitDisk :
    ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1}, p.1 ^ 2 + p.2 ^ 2 = π / 2 := by
  have h1 : ∫ p in unitDisk, (p.1 ^ 2 + p.2 ^ 2 : ℝ)
      = ∫ p : ℝ × ℝ, unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) p :=
    (integral_indicator measurableSet_unitDisk).symm
  have h2 : (∫ p : ℝ × ℝ, unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) p)
      = ∫ p in polarCoord.target,
          p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p) :=
    (integral_comp_polarCoord_symm _).symm
  have h3 : (∫ p in polarCoord.target,
        p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p))
      = ∫ p in Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π,
          p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p) := by
    rw [polarCoord_target]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo)
      (Set.prod_mono Ioc_subset_Ioi_self (subset_refl _))
      polar_integrand_off_box
  have h4 : (∫ p in Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π,
        p.1 • unitDisk.indicator (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (polarCoord.symm p))
      = ∫ p in Ioc (0:ℝ) 1 ×ˢ Ioo (-π) π, p.1 ^ 3 :=
    setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo) polar_integrand_on_box
  calc ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1}, (p.1 ^ 2 + p.2 ^ 2 : ℝ)
      = ∫ p in unitDisk, (p.1 ^ 2 + p.2 ^ 2 : ℝ) := rfl
    _ = _ := by rw [h1, h2, h3, h4, integral_box]

end Strang

/-- The volume under `z = x ^ 2 + y ^ 2` above the unit disk `x ^ 2 + y ^ 2 ≤ 1` is `π / 2`. -/
theorem strang_14_2_31 :
    ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1}, p.1 ^ 2 + p.2 ^ 2 = Real.pi / 2 :=
  Strang.volume_under_paraboloid_over_unitDisk
