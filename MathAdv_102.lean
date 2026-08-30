import Mathlib

/-!
# Wirtinger's inequality (Poincaré inequality on the circle)

If `f : ℝ → ℝ` is `T`-periodic, continuously differentiable, and has mean zero over a period,
then
`∫₀ᵀ |f|² ≤ (T² / (4π²)) ∫₀ᵀ |f'|²`.

The proof goes through **Parseval's identity** for Fourier series on an interval, together with
the relation between the Fourier coefficients of `f` and those of `f'`.
-/

open MeasureTheory Set intervalIntegral Complex

open scoped Real

namespace Wirtinger

/-- A continuous function is square integrable on a bounded interval. -/
private lemma memLp_two_of_continuous {g : ℝ → ℂ} (hg : Continuous g) (a b : ℝ) :
    MemLp g 2 (volume.restrict (Ioc a b)) := by
  have hfin : IsFiniteMeasure (volume.restrict (Ioc a b)) := by
    constructor
    simp [Real.volume_Ioc]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Ioc_subset_Icc_self hx))

/-- The zeroth Fourier coefficient of a mean-zero function vanishes. -/
private lemma fourierCoeffOn_zero_eq_zero {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ)
    (h_mean : ∫ t in (0)..T, f t = 0) :
    fourierCoeffOn hT (fun t => (f t : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp [intervalIntegral.integral_ofReal, h_mean]

/-- The key coefficient bound: for `n ≠ 0`, `‖c n‖ ≤ (T / (2π)) ‖c' n‖`. -/
private lemma norm_fourierCoeffOn_le {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ)
    (h_periodic : Function.Periodic f T) (hC1 : ContDiff ℝ 1 f) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hT (fun t => (f t : ℂ)) n‖
      ≤ (T / (2 * π)) * ‖fourierCoeffOn hT (fun t => ((deriv f t : ℝ) : ℂ)) n‖ := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t => (f t : ℂ)) (((deriv f x : ℝ) : ℂ)) x := fun x =>
    ((hC1.differentiable one_ne_zero x).hasDerivAt).ofReal_comp
  have hcont' : Continuous fun t => ((deriv f t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hC1.continuous_deriv le_rfl)
  have hint : IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ)) volume 0 T :=
    hcont'.intervalIntegrable _ _
  have hfT : (f T : ℂ) - (f 0 : ℂ) = 0 := by
    have := h_periodic 0
    simp only [zero_add] at this
    rw [this]
    ring
  have hkey := fourierCoeffOn_of_hasDerivAt hT hn (f := fun t => (f t : ℂ))
    (f' := fun t => ((deriv f t : ℝ) : ℂ)) (fun x _ => hderiv x) hint
  rw [hfT] at hkey
  rw [hkey]
  have hnorm : ‖(1 : ℂ) / (-2 * (π:ℂ) * I * (n:ℂ))‖ = 1 / (2 * π * |(n:ℝ)|) := by
    rw [norm_div]
    simp [abs_of_pos Real.pi_pos, mul_assoc]
  simp only [Complex.ofReal_zero, mul_zero, zero_sub, sub_zero, norm_neg, norm_mul, hnorm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have h2 : (1:ℤ) ≤ |n| := Int.one_le_abs (by simpa using hn)
    calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
      _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
      _ = |(n:ℝ)| := by push_cast [Int.cast_abs]; ring_nf
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hnn : 0 ≤ ‖fourierCoeffOn hT (fun t => ((deriv f t : ℝ) : ℂ)) n‖ := norm_nonneg _
  have hle : 1 / (2 * π * |(n:ℝ)|) * T ≤ T / (2 * π) := by
    have hstep : 1 / (2 * π * |(n:ℝ)|) ≤ 1 / (2 * π) := by
      apply one_div_le_one_div_of_le hpi
      nlinarith [Real.pi_pos]
    calc 1 / (2 * π * |(n:ℝ)|) * T ≤ 1 / (2 * π) * T :=
          mul_le_mul_of_nonneg_right hstep hT.le
      _ = T / (2 * π) := by ring
  nlinarith

end Wirtinger

open Wirtinger in
/-- **Wirtinger's inequality.** If `f` is `T`-periodic, continuously differentiable and has
zero mean over a period, then `∫₀ᵀ |f|² ≤ (T²/(4π²)) ∫₀ᵀ |f'|²`. -/
theorem stein_12
    {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ)
    (h_periodic : Function.Periodic f T)
    (hC1 : ContDiff ℝ 1 f)
    (h_mean : ∫ t in (0)..T, f t = 0) :
    ∫ t in (0)..T, (|f t| ^ (2 : ℕ) : ℝ)
      ≤ ((T ^ 2) / (4 * (Real.pi ^ 2)))
        * ∫ t in (0)..T, (|deriv f t| ^ (2 : ℕ) : ℝ) := by
  have hcont : Continuous fun t => (f t : ℂ) :=
    Complex.continuous_ofReal.comp (hC1.continuous)
  have hcont' : Continuous fun t => ((deriv f t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hC1.continuous_deriv le_rfl)
  have hS1 := hasSum_sq_fourierCoeffOn hT (memLp_two_of_continuous hcont 0 T)
  have hS2 := hasSum_sq_fourierCoeffOn hT (memLp_two_of_continuous hcont' 0 T)
  -- termwise bound on the squared coefficients
  have hterm : ∀ n : ℤ, ‖fourierCoeffOn hT (fun t => (f t : ℂ)) n‖ ^ 2
      ≤ (T / (2 * π)) ^ 2 * ‖fourierCoeffOn hT (fun t => ((deriv f t : ℝ) : ℂ)) n‖ ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [fourierCoeffOn_zero_eq_zero hT f h_mean]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have h := norm_fourierCoeffOn_le hT f h_periodic hC1 hn
      have h0 : (0:ℝ) ≤ ‖fourierCoeffOn hT (fun t => (f t : ℂ)) n‖ := norm_nonneg _
      nlinarith [norm_nonneg (fourierCoeffOn hT (fun t => ((deriv f t : ℝ) : ℂ)) n),
        div_nonneg hT.le (by positivity : (0:ℝ) ≤ 2 * π)]
  have hsum : ∑' n : ℤ, ‖fourierCoeffOn hT (fun t => (f t : ℂ)) n‖ ^ 2
      ≤ (T / (2 * π)) ^ 2 * ∑' n : ℤ, ‖fourierCoeffOn hT (fun t => ((deriv f t : ℝ) : ℂ)) n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hS1.summable (hS2.summable.mul_left _)
  rw [hS1.tsum_eq, hS2.tsum_eq] at hsum
  simp only [sub_zero, smul_eq_mul] at hsum
  -- rewrite the complex norms as real absolute values
  have e1 : ∫ x in (0:ℝ)..T, ‖((f x : ℂ))‖ ^ 2 = ∫ t in (0:ℝ)..T, (|f t| ^ (2 : ℕ) : ℝ) := by
    simp
  have e2 : ∫ x in (0:ℝ)..T, ‖(((deriv f x : ℝ) : ℂ))‖ ^ 2
      = ∫ t in (0:ℝ)..T, (|deriv f t| ^ (2 : ℕ) : ℝ) := by
    simp
  rw [e1, e2] at hsum
  have hfac : (T / (2 * π)) ^ 2 = T ^ 2 / (4 * π ^ 2) := by
    rw [div_pow]; ring_nf
  rw [hfac] at hsum
  have := mul_le_mul_of_nonneg_left hsum hT.le
  calc ∫ t in (0:ℝ)..T, (|f t| ^ (2 : ℕ) : ℝ)
      = T * (T⁻¹ * ∫ t in (0:ℝ)..T, (|f t| ^ (2 : ℕ) : ℝ)) := by
        field_simp
    _ ≤ T * (T ^ 2 / (4 * π ^ 2) * (T⁻¹ * ∫ t in (0:ℝ)..T, (|deriv f t| ^ (2 : ℕ) : ℝ))) := this
    _ = T ^ 2 / (4 * π ^ 2) * ∫ t in (0:ℝ)..T, (|deriv f t| ^ (2 : ℕ) : ℝ) := by
        field_simp
