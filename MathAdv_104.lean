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

open Filter Complex MeasureTheory

/-- The `n`-th Fourier coefficient of a `2π`-periodic function `f : ℝ → ℂ`. -/
noncomputable def steinFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * Real.pi)) *
    ∫ x in (0 : ℝ)..(2 * Real.pi),
      f x * Complex.exp (-(n : ℂ) * Complex.I * x)

/-- The derivative of a periodic function is periodic. -/
theorem periodic_deriv_of_periodic {f : ℝ → ℂ} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have h1 : deriv (fun y : ℝ => f (y + c)) x = deriv f (x + c) := deriv_comp_add_const f c x
  rw [h.funext] at h1
  exact h1.symm

/-- Integration by parts: for a `C¹` periodic function, the (unnormalized) Fourier coefficient
of the derivative equals `i n` times that of the function. -/
theorem integral_deriv_mul_exp (f : ℝ → ℂ) (n : ℤ)
    (hp : Function.Periodic f (2 * Real.pi)) (hf : ContDiff ℝ 1 f) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), deriv f x * Complex.exp (-(n : ℂ) * Complex.I * x))
      = ((n : ℂ) * Complex.I) *
        ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Complex.exp (-(n : ℂ) * Complex.I * x) := by
  set c : ℂ := -(n : ℂ) * Complex.I with hc
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hD : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y * Complex.exp (c * y))
      (deriv f x * Complex.exp (c * x) + f x * (Complex.exp (c * x) * c)) x := by
    intro x
    have h1 : HasDerivAt f (deriv f x) x := (hf.differentiable one_ne_zero x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => (c * y)) c x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    exact h1.mul h2.cexp
  have hi1 : IntervalIntegrable (fun x : ℝ => deriv f x * Complex.exp (c * x))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous fun x : ℝ => deriv f x * Complex.exp (c * x)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => f x * (Complex.exp (c * x) * c))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous fun x : ℝ => f x * (Complex.exp (c * x) * c)).intervalIntegrable _ _
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => f y * Complex.exp (c * y)) (fun x _ => hD x) (hi1.add hi2)
  have hzero : f (2 * Real.pi) * Complex.exp (c * (2 * Real.pi : ℝ))
      - f 0 * Complex.exp (c * (0 : ℝ)) = 0 := by
    have h1 : f (2 * Real.pi) = f 0 := by simpa using hp 0
    have h2 : Complex.exp (c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have h3 : c * ((2 * Real.pi : ℝ) : ℂ) = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast [hc]; ring
      rw [h3, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1, h2]
    simp
  rw [hzero, intervalIntegral.integral_add hi1 hi2] at hsub
  have hrw : (∫ x in (0 : ℝ)..(2 * Real.pi), f x * (Complex.exp (c * x) * c))
      = c * ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Complex.exp (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  rw [hrw] at hsub
  have hfin : (∫ x in (0 : ℝ)..(2 * Real.pi), deriv f x * Complex.exp (c * x))
      = -c * ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Complex.exp (c * x) := by
    linear_combination hsub
  rw [hfin, hc]
  ring

/-- Iterating integration by parts `k` times. -/
theorem integral_iterate_deriv_mul_exp (k : ℕ) :
    ∀ (f : ℝ → ℂ), Function.Periodic f (2 * Real.pi) → ContDiff ℝ k f → ∀ n : ℤ,
    (∫ x in (0 : ℝ)..(2 * Real.pi), deriv^[k] f x * Complex.exp (-(n : ℂ) * Complex.I * x))
      = ((n : ℂ) * Complex.I) ^ k *
        ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Complex.exp (-(n : ℂ) * Complex.I * x) := by
  induction k with
  | zero => intro f _ _ n; simp
  | succ k ih =>
      intro f hp hf n
      have h1 : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
      rw [Function.iterate_succ_apply,
        ih (deriv f) (periodic_deriv_of_periodic hp) (ContDiff.deriv' hf) n,
        integral_deriv_mul_exp f n hp (hf.of_le h1)]
      ring

/-- **Riemann–Lebesgue lemma** on the interval `[0, 2π]`, along the integer frequencies:
the integrals `∫₀^{2π} g(x) e^{-inx} dx` tend to `0` as `|n| → ∞`. -/
theorem riemann_lebesgue_int (g : ℝ → ℂ) :
    Tendsto (fun n : ℤ => ∫ x in (0 : ℝ)..(2 * Real.pi),
        g x * Complex.exp (-(n : ℂ) * Complex.I * x)) cofinite (nhds 0) := by
  set G : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) g with hG
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkey : ∀ w : ℝ, (∫ v : ℝ, (Real.fourierChar (-(v * w)) : Circle) • G v)
      = ∫ x in (0 : ℝ)..(2 * Real.pi),
          g x * Complex.exp (2 * Real.pi * (-(x * w)) * Complex.I) := by
    intro w
    have h1 : ∀ v : ℝ, (Real.fourierChar (-(v * w)) : Circle) • G v
        = Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi))
            (fun x => g x * Complex.exp (2 * Real.pi * (-(x * w)) * Complex.I)) v := by
      intro v
      rw [Circle.smul_def, Real.fourierChar_apply, hG]
      by_cases hv : v ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_eq_mul, mul_zero]
    simp_rw [h1]
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hpi]
  have hRL := Real.tendsto_integral_exp_smul_cocompact G
  have hφ : Tendsto (fun n : ℤ => (n : ℝ) / (2 * Real.pi)) cofinite (cocompact ℝ) := by
    have h2 : Tendsto (fun x : ℝ => x * (2 * Real.pi)⁻¹) (cocompact ℝ) (cocompact ℝ) :=
      Filter.tendsto_cocompact_mul_right₀ (by positivity)
    simpa [div_eq_mul_inv, Function.comp_def] using h2.comp Int.tendsto_coe_cofinite
  refine (hRL.comp hφ).congr ?_
  intro n
  simp only [Function.comp_apply]
  rw [hkey]
  congr 1
  funext x
  congr 1
  push_cast
  field_simp

/-- **Decay of Fourier coefficients of a `C^k` function.**
If `f` is `2π`-periodic and of class `C^k`, then `n^k * f̂(n) → 0` as `|n| → ∞`. -/
theorem stein_14
    (f : ℝ → ℂ) (k : ℕ)
    (h_periodic : Function.Periodic f (2 * Real.pi))
    (h_Ck : ContDiff ℝ k f) :
    Filter.Tendsto (fun n : ℤ => ((n : ℂ) ^ k) * steinFourierCoeff f n)
      Filter.cofinite (nhds 0) := by
  have key : ∀ n : ℤ, ((n : ℂ) ^ k) * steinFourierCoeff f n
      = (1 / (2 * Real.pi) : ℂ) * (Complex.I ^ k)⁻¹ *
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          deriv^[k] f x * Complex.exp (-(n : ℂ) * Complex.I * x) := by
    intro n
    rw [integral_iterate_deriv_mul_exp k f h_periodic h_Ck n, steinFourierCoeff]
    have hI : (Complex.I ^ k) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    field_simp [mul_pow]
    ring
  simp only [key]
  have hRL := riemann_lebesgue_int (deriv^[k] f)
  simpa using hRL.const_mul ((1 / (2 * Real.pi) : ℂ) * (Complex.I ^ k)⁻¹)
