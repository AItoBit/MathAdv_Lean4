import Mathlib

/-!
# `∑_{n ∈ ℤ} 1/(n+α)² = π²/sin²(πα)` for non-integer real `α`

This file proves the classical identity

`∑' n : ℤ, 1/(n + α)^2 = π^2 / sin(π α)^2`   (`tsum_one_div_add_sq_eq_pi_sq_div_sin_sq`)

for every real `α` which is not an integer.

The proof is an application of **Parseval's identity** on the circle (the answer to the
multiple-choice question accompanying the problem): we apply Parseval to the function
`x ↦ exp (2πi α x)` on the interval `(0,1]`, whose `n`-th Fourier coefficient is
`(exp (2πi α) - 1) / (2πi (α - n))`, of squared norm `sin(πα)^2 / (π^2 (α-n)^2)`, while the
mean square of the function itself is `1`.

Note on the statement supplied with the problem: the sum `∑' n : ℤ, 1/n^2` appearing there does
not depend on `α` (and equals `π²/3` with Lean's junk value `1/0 = 0`), so that statement is
false; the intended summand is `1/(n+α)^2`, which is what is proved here.  The original
statement is kept, commented out, at the end of the file.
-/

open Complex MeasureTheory intervalIntegral

namespace SteinParseval

/-- The function to which Parseval's identity is applied. -/
noncomputable def expChar (a : ℝ) : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * I * a * x)

lemma norm_expChar (a x : ℝ) : ‖expChar a x‖ = 1 := by
  simp [expChar, Complex.norm_exp]

lemma continuous_expChar (a : ℝ) : Continuous (expChar a) := by
  unfold expChar
  fun_prop

lemma memLp_expChar (a : ℝ) : MemLp (expChar a) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    constructor
    simp
  exact MemLp.of_bound (continuous_expChar a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simp [norm_expChar])

/-- The `n`-th Fourier coefficient of `x ↦ exp (2πi α x)` on `(0,1]`. -/
lemma fourierCoeffOn_expChar (a : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) :
    fourierCoeffOn (zero_lt_one' ℝ) (expChar a) n =
      (Complex.exp (2 * Real.pi * I * a) - 1) / (2 * Real.pi * I * (a - n)) := by
  have hc : (2 * Real.pi * I * ((a : ℂ) - n)) ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2 : ((a : ℂ) - n) ≠ 0 := by
      have : a - (n : ℝ) ≠ 0 := sub_ne_zero.2 (ha n)
      simpa [sub_eq_zero] using (by exact_mod_cast this : ((a : ℂ) - (n : ℂ)) ≠ 0)
    simp [h1, h2, Complex.I_ne_zero]
  rw [fourierCoeffOn_eq_integral]
  have hint : ∀ x : ℝ, (fourier (-n) ((x : ℝ) : AddCircle ((1:ℝ) - 0))) • expChar a x
      = Complex.exp ((2 * Real.pi * I * ((a : ℂ) - n)) * x) := by
    intro x
    rw [fourier_coe_apply]
    simp only [expChar, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [hint]
  rw [integral_exp_mul_complex hc]
  simp only [sub_zero, one_div, inv_one, one_smul, Complex.ofReal_one, mul_one,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have key : Complex.exp (2 * (Real.pi : ℂ) * I * ((a : ℂ) - n))
      = Complex.exp (2 * (Real.pi : ℂ) * I * a) := by
    rw [show (2 * (Real.pi : ℂ) * I * ((a : ℂ) - n))
        = 2 * (Real.pi : ℂ) * I * a - (n : ℂ) * (2 * Real.pi * I) by ring,
      Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  rw [key]

/-- The squared norm of the `n`-th Fourier coefficient. -/
lemma norm_sq_fourierCoeffOn_expChar (a : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ)) (n : ℤ) :
    ‖fourierCoeffOn (zero_lt_one' ℝ) (expChar a) n‖ ^ 2 =
      Real.sin (Real.pi * a) ^ 2 / (Real.pi ^ 2 * (a - n) ^ 2) := by
  rw [fourierCoeffOn_expChar a ha n, norm_div, div_pow]
  have hnum : ‖Complex.exp (2 * (Real.pi : ℂ) * I * a) - 1‖ ^ 2
      = 4 * Real.sin (Real.pi * a) ^ 2 := by
    have hz : (2 * (Real.pi : ℂ) * I * a) = ((2 * Real.pi * a : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hz, Complex.exp_mul_I]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.cos_ofReal_re, Complex.one_re, Complex.one_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_im]
    have hcos : Real.cos (2 * Real.pi * a) = 1 - 2 * Real.sin (Real.pi * a) ^ 2 := by
      rw [show (2 * Real.pi * a) = 2 * (Real.pi * a) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * a)]
    have hsin : Real.sin (2 * Real.pi * a) = 2 * Real.sin (Real.pi * a) * Real.cos (Real.pi * a) :=
      by rw [show (2 * Real.pi * a) = 2 * (Real.pi * a) by ring, Real.sin_two_mul]
    have hpyth := Real.sin_sq_add_cos_sq (Real.pi * a)
    rw [hcos, hsin]
    nlinarith [hpyth]
  have hden : ‖2 * (Real.pi : ℂ) * I * ((a : ℂ) - n)‖ ^ 2 = 4 * (Real.pi ^ 2 * (a - n) ^ 2) := by
    have : ‖2 * (Real.pi : ℂ) * I * ((a : ℂ) - n)‖ = 2 * |Real.pi| * |a - n| := by
      rw [show (2 * (Real.pi : ℂ) * I * ((a : ℂ) - n)) = ((2 * Real.pi * (a - n) : ℝ) : ℂ) * I by
        push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul, abs_mul]
      simp
    rw [this]
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (by norm_num : (4:ℝ) ≠ 0)]

lemma integral_norm_sq_expChar (a : ℝ) :
    ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖expChar a x‖ ^ 2 = 1 := by
  simp [norm_expChar]

/-- Parseval's identity applied to `x ↦ exp (2πi α x)` on `(0,1]`. -/
lemma hasSum_sin_sq_div (a : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ)) :
    HasSum (fun n : ℤ => Real.sin (Real.pi * a) ^ 2 / (Real.pi ^ 2 * (a - n) ^ 2)) 1 := by
  have h := hasSum_sq_fourierCoeffOn (zero_lt_one' ℝ) (memLp_expChar a)
  rw [integral_norm_sq_expChar a] at h
  simpa only [norm_sq_fourierCoeffOn_expChar a ha] using h

lemma sin_pi_mul_ne_zero (a : ℝ) (ha : ∀ m : ℤ, a ≠ (m : ℝ)) : Real.sin (Real.pi * a) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ha m ?_
  have h2 : Real.pi * (m : ℝ) = Real.pi * a := by linear_combination hm
  exact (mul_left_cancel₀ Real.pi_ne_zero h2).symm

/-- **Main result.** For real non-integer `α`,
`∑' n : ℤ, 1/(n + α)^2 = π^2 / sin(π α)^2`. -/
theorem tsum_one_div_add_sq_eq_pi_sq_div_sin_sq (α : ℝ) (hα : ∀ m : ℤ, α ≠ (m : ℝ)) :
    (∑' n : ℤ, (1 : ℝ) / ((n : ℝ) + α) ^ 2) = Real.pi ^ 2 / (Real.sin (Real.pi * α)) ^ 2 := by
  have hs := hasSum_sin_sq_div α hα
  have hsin : Real.sin (Real.pi * α) ≠ 0 := sin_pi_mul_ne_zero α hα
  have hsin2 : Real.sin (Real.pi * α) ^ 2 ≠ 0 := pow_ne_zero _ hsin
  have hpi2 : (Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  -- rescale
  have hs2 : HasSum (fun n : ℤ => (1 : ℝ) / (α - n) ^ 2)
      (Real.pi ^ 2 / Real.sin (Real.pi * α) ^ 2) := by
    have := hs.mul_left (Real.pi ^ 2 / Real.sin (Real.pi * α) ^ 2)
    rw [mul_one] at this
    refine this.congr_fun ?_
    intro n
    by_cases hn : α - (n : ℝ) = 0
    · simp [hn]
    · have hd : (α - (n : ℝ)) ^ 2 ≠ 0 := pow_ne_zero _ hn
      have hden : Real.sin (Real.pi * α) ^ 2 * (Real.pi ^ 2 * (α - (n : ℝ)) ^ 2) ≠ 0 :=
        mul_ne_zero hsin2 (mul_ne_zero hpi2 hd)
      rw [div_mul_div_comm, div_eq_div_iff hd hden]
      ring
  have hs3 : HasSum (fun n : ℤ => (1 : ℝ) / ((n : ℝ) + α) ^ 2)
      (Real.pi ^ 2 / Real.sin (Real.pi * α) ^ 2) := by
    have := (Equiv.neg ℤ).hasSum_iff.mpr hs2
    refine this.congr_fun ?_
    intro n
    simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
    ring_nf
  exact hs3.tsum_eq



end SteinParseval

/-- Corrected form of the originally supplied statement `stein_16`: for real non-integer `α`,
`∑' n : ℤ, 1/(n + α)^2 = π^2 / sin(π α)^2`.  (The summand in the original statement,
`1/n^2`, does not involve `α`; see the comment above.) -/
theorem stein_16' (α : ℝ) (hα : ∀ m : ℤ, α ≠ (m : ℝ)) :
    (∑' n : ℤ, (1 : ℝ) / ((n : ℝ) + α) ^ 2) = Real.pi ^ 2 / (Real.sin (Real.pi * α)) ^ 2 :=
  SteinParseval.tsum_one_div_add_sq_eq_pi_sq_div_sin_sq α hα
