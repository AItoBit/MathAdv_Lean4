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

open Real Complex MeasureTheory intervalIntegral Set
open scoped Interval

/-- The Fourier coefficient of `f : ℝ → ℂ`, viewed as a `2π`-periodic function. -/
noncomputable def myFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * Real.pi)) *
    (∫ x in (0)..(2 * Real.pi),
      f x * Complex.exp (-Complex.I * (n : ℝ) * x))

lemma twoPi_pos : (0:ℝ) < 2 * Real.pi := by positivity

/-- `myFourierCoeff` agrees with Mathlib's `fourierCoeffOn` on `[0, 2π]`. -/
lemma myFourierCoeff_eq (f : ℝ → ℂ) (n : ℤ) :
    myFourierCoeff f n = fourierCoeffOn twoPi_pos f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [myFourierCoeff, sub_zero, smul_eq_mul, Complex.real_smul, fourier_coe_apply,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  congr 1
  ext x
  push_cast
  rw [show (2 * (Real.pi:ℂ) * Complex.I * (-n) * x / (2 * Real.pi)) = -Complex.I * n * x by
    field_simp]
  ring

/-- Integration by parts: for `n ≠ 0`, the `n`-th Fourier coefficient of a `2π`-periodic `C¹`
function `f` has norm `‖ĝ n‖ / |n|`, where `g = f'` is the derivative of `f`. -/
lemma norm_fourierCoeffOn_eq_of_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (2 * Real.pi))
    (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn twoPi_pos f n‖ = ‖fourierCoeffOn twoPi_pos (deriv f) n‖ / |(n:ℝ)| := by
  have hd : ∀ x ∈ [[(0:ℝ), 2 * Real.pi]], HasDerivAt f (deriv f x) x := fun x _ =>
    (hf.differentiable one_ne_zero x).hasDerivAt
  have hdi : IntervalIntegrable (deriv f) volume 0 (2 * Real.pi) :=
    (hf.continuous_deriv le_rfl).intervalIntegrable _ _
  have key := fourierCoeffOn_of_hasDerivAt twoPi_pos hn hd hdi
  have hfp : f (2 * Real.pi) - f 0 = 0 := by
    have := hper 0
    simp only [zero_add] at this
    rw [this]; ring
  rw [hfp, mul_zero, zero_sub, ← mul_neg] at key
  rw [key, norm_mul, norm_mul, norm_neg, norm_div, norm_one]
  have h2 : ‖(-2 * (Real.pi:ℂ) * Complex.I * n)‖ = 2 * Real.pi * |(n:ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  have h3 : ‖((2 * Real.pi:ℝ):ℂ) - ((0:ℝ):ℂ)‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [h2, h3]
  have _hnz : |(n:ℝ)| ≠ 0 := by
    simp only [ne_eq, abs_eq_zero, Int.cast_eq_zero]
    exact_mod_cast hn
  have _hpi : (Real.pi:ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Bessel's inequality, a consequence of Parseval's identity: the squared norms of the
Fourier coefficients of a continuous function are summable. -/
lemma summable_sq_fourierCoeffOn (g : ℝ → ℂ) (hg : Continuous g) :
    Summable (fun n : ℤ => ‖fourierCoeffOn twoPi_pos g n‖ ^ 2) := by
  have _hfm : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))) := by
    constructor
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
    finiteness
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hg.continuousOn
  have hL2 : MemLp g 2 (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))) := by
    refine MemLp.of_bound hg.aestronglyMeasurable C ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    exact hC x ⟨hx.1.le, hx.2⟩
  exact (hasSum_sq_fourierCoeffOn twoPi_pos hL2).summable

/-- **The Fourier series of a continuously differentiable function on the circle converges
absolutely.** The proof combines integration by parts (relating the Fourier coefficients of `f`
to those of `f'`) with Parseval's identity for `f'` and the Cauchy-Schwarz / AM-GM estimate
`‖ĝ n‖ / |n| ≤ (1/n² + ‖ĝ n‖²)/2`. -/
theorem stein_15
    (f : ℝ → ℂ)
    (hf_c1 : ContDiff ℝ 1 f)
    (hf_periodic : Function.Periodic f (2 * Real.pi)) :
    Summable (fun n : ℤ => ‖myFourierCoeff f n‖) := by
  have hsq := summable_sq_fourierCoeffOn (deriv f) (hf_c1.continuous_deriv le_rfl)
  have hinv : Summable (fun n : ℤ => 1 / (n:ℝ)^2) := summable_one_div_int_pow.mpr one_lt_two
  have hfin : Summable (fun n : ℤ => if n = 0 then ‖myFourierCoeff f 0‖ else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Set.finite_singleton (0:ℤ))
    intro x hx
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hx
    simpa using hx.1
  have hmaj : Summable (fun n : ℤ =>
      (1/2) * (1 / (n:ℝ)^2 + ‖fourierCoeffOn twoPi_pos (deriv f) n‖ ^ 2)
        + (if n = 0 then ‖myFourierCoeff f 0‖ else 0)) :=
    ((hinv.add hsq).mul_left (1/2)).add hfin
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hmaj
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ite_true]
    have h0 : (0:ℝ) ≤ (1/2) * (1 / ((0:ℤ):ℝ)^2 + ‖fourierCoeffOn twoPi_pos (deriv f) 0‖ ^ 2) := by
      positivity
    linarith
  · simp only [if_neg hn, add_zero]
    rw [myFourierCoeff_eq, norm_fourierCoeffOn_eq_of_periodic f hf_c1 hf_periodic n hn]
    have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    have _hpos : (0:ℝ) < |(n:ℝ)| := lt_of_lt_of_le one_pos h1
    set a := ‖fourierCoeffOn twoPi_pos (deriv f) n‖
    have e1 : (1:ℝ)/(n:ℝ)^2 = (1/|(n:ℝ)|)^2 := by rw [div_pow, one_pow, sq_abs]
    have e2 : a / |(n:ℝ)| = a * (1/|(n:ℝ)|) := by ring
    rw [e1, e2]
    nlinarith [sq_nonneg (a - 1/|(n:ℝ)|)]

/-- Answer to the accompanying multiple-choice question: **(c) Parseval's identity**. -/
def stein_15_answer : String := "(c) Parseval's identity"
