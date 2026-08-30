import Mathlib

open scoped Real
open Complex MeasureTheory

/-!
# `∑_{n ∈ ℤ} 1/(n+α)² = π²/sin²(πα)` for `α` not an integer

The proof is the classical one via **Parseval's identity**: the function
`f α x = exp (-2πiαx)` on the circle `ℝ / ℤ` has `n`-th Fourier coefficient
`(exp(-2πiα) - 1) / (-2πi(α+n))`, of squared modulus
`sin²(πα)/π² · 1/(n+α)²`, while its `L²` norm on `[0,1]` is `1`.
-/

namespace Stein11

/-- The exponential function whose Fourier coefficients on `[0,1]` produce the series
`∑ 1/(n+α)²`. -/
noncomputable def f (α : ℝ) : ℝ → ℂ := fun x => Complex.exp (-(2 * π * Complex.I * α) * x)

lemma norm_f (α : ℝ) (x : ℝ) : ‖f α x‖ = 1 := by
  simp [f, Complex.norm_exp]

lemma continuous_f (α : ℝ) : Continuous (f α) := by
  unfold f; fun_prop

lemma memLp_f (α : ℝ) : MemLp (f α) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  exact MemLp.of_bound (continuous_f α).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simp [norm_f])

lemma integral_norm_sq_f (α : ℝ) : (∫ x in (0 : ℝ)..1, ‖f α x‖ ^ 2) = 1 := by
  simp [norm_f]

/-- The `n`-th Fourier coefficient of `f α` on `[0,1]`. -/
lemma fourierCoeffOn_f (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (n : ℤ) :
    fourierCoeffOn (zero_lt_one' ℝ) (f α) n =
      (Complex.exp (-(2 * π * Complex.I * α)) - 1) / (-(2 * π * Complex.I * (α + n))) := by
  have hc : (-(2 * π * Complex.I * ((α : ℂ) + n)) : ℂ) ≠ 0 := by
    simp only [neg_ne_zero, mul_ne_zero_iff]
    refine ⟨⟨⟨by norm_num, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩, ?_⟩
    intro h
    have h2 : (α : ℝ) + n = 0 := by exact_mod_cast h
    exact hα (-n) (by push_cast; linarith)
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, f, sub_zero, smul_eq_mul, ← Complex.exp_add]
  have key : ∀ x : ℝ,
      (2 * π * Complex.I * ((-n : ℤ) : ℂ) * x / ((1 : ℝ) : ℂ)) + (-(2 * π * Complex.I * α) * x)
        = (-(2 * π * Complex.I * ((α : ℂ) + n))) * x := by
    intro x; push_cast; ring
  simp only [key]
  rw [integral_exp_mul_complex hc]
  have hn : Complex.exp (-(2 * π * Complex.I * ((α : ℂ) + n)))
      = Complex.exp (-(2 * π * Complex.I * α)) := by
    rw [show (-(2 * π * Complex.I * ((α : ℂ) + n)))
        = -(2 * π * Complex.I * α) + ((-n : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    ring
  push_cast
  simp [hn]

lemma norm_sq_exp_sub_one (α : ℝ) :
    ‖Complex.exp (-(2 * π * Complex.I * α)) - 1‖ ^ 2 = 4 * Real.sin (π * α) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [show (-(2 * π * Complex.I * (α : ℂ))) = ((-(2 * π * α) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
  have h2 : Real.cos (-(2 * π * α)) = 1 - 2 * Real.sin (π * α) ^ 2 := by
    rw [Real.cos_neg, show (2 * π * α) = 2 * (π * α) by ring, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (π * α)]
  have h3 : Real.sin (-(2 * π * α)) = -(2 * Real.sin (π * α) * Real.cos (π * α)) := by
    rw [Real.sin_neg, show (2 * π * α) = 2 * (π * α) by ring, Real.sin_two_mul]
  rw [h2, h3]
  nlinarith [Real.sin_sq_add_cos_sq (π * α)]

lemma sin_pi_mul_ne_zero (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) : Real.sin (π * α) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  exact hα n (mul_left_cancel₀ Real.pi_ne_zero (by linarith : π * α = π * (n : ℝ)))

lemma norm_sq_coeff (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) (n : ℤ) :
    ‖fourierCoeffOn (zero_lt_one' ℝ) (f α) n‖ ^ 2 =
      (Real.sin (π * α) ^ 2 / π ^ 2) * (1 / ((n : ℝ) + α) ^ 2) := by
  have hne : ((n : ℝ) + α) ≠ 0 := fun h => hα (-n) (by push_cast; linarith)
  rw [fourierCoeffOn_f α hα n, norm_div, div_pow, norm_sq_exp_sub_one]
  have hd : ‖(-(2 * π * Complex.I * ((α : ℂ) + n)))‖ ^ 2 = 4 * π ^ 2 * ((n : ℝ) + α) ^ 2 := by
    rw [show (-(2 * π * Complex.I * ((α : ℂ) + n)))
        = ((-(2 * π * ((n : ℝ) + α)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hd]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

end Stein11

open Stein11 in
/-- For `α` not an integer, `∑_{n = -∞}^{∞} 1/(n+α)² = π²/sin²(πα)`. -/
theorem stein_11 (α : ℝ) (hα : ∀ n : ℤ, α ≠ n) :
  (∑' (n : ℤ), (1 : ℝ) / ((n : ℝ) + α) ^ 2) =
    Real.pi ^ 2 / (Real.sin (Real.pi * α)) ^ 2 := by
  have key := tsum_sq_fourierCoeffOn (zero_lt_one' ℝ) (memLp_f α)
  rw [integral_norm_sq_f α] at key
  simp only [norm_sq_coeff α hα] at key
  rw [tsum_mul_left] at key
  have hs : Real.sin (π * α) ≠ 0 := sin_pi_mul_ne_zero α hα
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [smul_eq_mul, sub_zero, inv_one, one_mul] at key
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq (pow_ne_zero 2 hpi)] at key
  rw [eq_div_iff (pow_ne_zero 2 hs)]
  linear_combination key
