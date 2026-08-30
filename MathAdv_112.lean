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

noncomputable def heaviside (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else 0

noncomputable def kammlerU (α : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (-α * x) : ℂ) * ((heaviside x : ℝ) : ℂ)

noncomputable def kammlerConv (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, f t * g (x - t)

noncomputable def kammlerFourier (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-2 * Real.pi * Complex.I * (s : ℂ) * x)

noncomputable def kammlerUPow (α : ℝ) : ℕ → ℝ → ℂ
  | 0       => fun _ => 0
  | 1       => kammlerU α
  | n + 2   => kammlerConv (kammlerUPow α (n + 1)) (kammlerU α)

section KammlerAux

open MeasureTheory Set Filter Topology

/-- The explicit form of the `n+1`-fold convolution power of `u`. -/
noncomputable def kammlerG (α : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((x ^ n / n ! : ℝ) : ℂ) * (Real.exp (-α * x) : ℂ) * ((heaviside x : ℝ) : ℂ)

lemma kammler_norm_pow_mul_exp (n : ℕ) (b : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖(x : ℂ) ^ n * Complex.exp (-(b * x))‖ = x ^ n * Real.exp (-b.re * x) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx, Complex.norm_exp]
  simp [Complex.mul_re]

lemma kammler_integrableOn_pow_exp (n : ℕ) {b : ℂ} (hb : 0 < b.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-(b * x))) (Ioi 0) := by
  have hn : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hreal : IntegrableOn (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-b.re * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hn zero_lt_one hb
  have hreal' : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-b.re * x)) (Ioi 0) := by
    refine hreal.congr_fun (fun x _ => ?_) measurableSet_Ioi
    dsimp
    rw [Real.rpow_natCast, Real.rpow_one]
  refine Integrable.mono' hreal' (Continuous.aestronglyMeasurable (by fun_prop)).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [kammler_norm_pow_mul_exp n b (le_of_lt hx)]

lemma kammler_tendsto_pow_exp (n : ℕ) {b : ℂ} (hb : 0 < b.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ n * Complex.exp (-(b * x))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b.re hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [kammler_norm_pow_mul_exp n b hx.le, Real.rpow_natCast]

lemma kammler_integral_pow_exp {b : ℂ} (hb : 0 < b.re) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ n * Complex.exp (-(b * x)) = (n ! : ℂ) / b ^ (n + 1) := by
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  induction n with
  | zero =>
      have hdC : ∀ z : ℂ, HasDerivAt (fun z : ℂ => -Complex.exp (-(b * z)) / b)
          (Complex.exp (-(b * z))) z := by
        intro z
        have h1 : HasDerivAt (fun w : ℂ => -(b * w)) (-b) z := by
          simpa using (hasDerivAt_id z).const_mul (-b)
        have h2 := (Complex.hasDerivAt_exp (-(b * z))).comp z h1
        have h3 := (h2.neg).div_const b
        have hcancel : -(-b * Complex.exp (-(b * z))) / b = Complex.exp (-(b * z)) := by
          calc -(-b * Complex.exp (-(b * z))) / b
            _ = (b * Complex.exp (-(b * z))) / b := by ring
            _ = Complex.exp (-(b * z)) := mul_div_cancel_left₀ (Complex.exp (-(b * z))) hb0
        exact hcancel ▸ h3
      have key := integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun x : ℝ => -Complex.exp (-(b * x)) / b)
        (f' := fun x : ℝ => Complex.exp (-(b * x))) (a := 0) (m := 0)
        (by fun_prop)
        (fun x _ => (hdC (x : ℂ)).comp_ofReal)
        (by simpa using kammler_integrableOn_pow_exp 0 hb)
        (by
          have h := kammler_tendsto_pow_exp 0 hb
          simp only [pow_zero, one_mul] at h
          simpa using h.neg.div_const b)
      simp only [pow_zero, one_mul]
      rw [key]
      simp only [mul_zero, neg_zero, Complex.ofReal_zero, Complex.exp_zero, neg_neg, sub_zero]
      ring
  | succ n ih =>
      have hdC : ∀ z : ℂ, HasDerivAt (fun z : ℂ => -(z ^ (n + 1) * Complex.exp (-(b * z))) / b)
          ((z ^ (n + 1) * Complex.exp (-(b * z))
            - ((n : ℂ) + 1) / b * (z ^ n * Complex.exp (-(b * z))))) z := by
        intro z
        have h1 : HasDerivAt (fun w : ℂ => -(b * w)) (-b) z := by
          simpa using (hasDerivAt_id z).const_mul (-b)
        have h2 := (Complex.hasDerivAt_exp (-(b * z))).comp z h1
        have h3 : HasDerivAt (fun z : ℂ => z ^ (n + 1)) ((n + 1 : ℕ) * z ^ n) z := by
          simpa using hasDerivAt_pow (n + 1) z
        have h4 := h3.mul h2
        have h5 := (h4.neg).div_const b
        convert h5 using 1
        push_cast
        field_simp
        ring
      have hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (n + 1) * Complex.exp (-(b * x))
          - ((n : ℂ) + 1) / b * ((x : ℂ) ^ n * Complex.exp (-(b * x)))) (Ioi 0) :=
        (kammler_integrableOn_pow_exp (n + 1) hb).sub
          ((kammler_integrableOn_pow_exp n hb).const_mul _)
      have htend : Tendsto (fun x : ℝ => -((x : ℂ) ^ (n + 1) * Complex.exp (-(b * x))) / b)
          atTop (𝓝 0) := by
        simpa using ((kammler_tendsto_pow_exp (n + 1) hb).neg.div_const b)
      have key := integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun x : ℝ => -((x : ℂ) ^ (n + 1) * Complex.exp (-(b * x))) / b)
        (f' := fun x : ℝ => (x : ℂ) ^ (n + 1) * Complex.exp (-(b * x))
            - ((n : ℂ) + 1) / b * ((x : ℂ) ^ n * Complex.exp (-(b * x)))) (a := 0) (m := 0)
        (by fun_prop) (fun x _ => (hdC (x : ℂ)).comp_ofReal) hint htend
      simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero n), zero_mul, neg_zero,
        zero_div, sub_zero] at key
      rw [integral_sub (kammler_integrableOn_pow_exp (n + 1) hb)
          ((kammler_integrableOn_pow_exp n hb).const_mul _), integral_const_mul, ih] at key
      have h2 : (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (n + 1) * Complex.exp (-(b * x)))
          = ((n : ℂ) + 1) / b * ((n ! : ℂ) / b ^ (n + 1)) := by linear_combination key
      rw [h2, Nat.factorial_succ]
      push_cast
      field_simp
      ring

lemma kammler_conv_step (α : ℝ) (n : ℕ) :
    kammlerConv (kammlerG α n) (kammlerU α) = kammlerG α (n + 1) := by
  funext x
  rcases le_or_gt x 0 with hx | hx
  · have hzero : kammlerConv (kammlerG α n) (kammlerU α) x = 0 := by
      rw [kammlerConv]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      rcases lt_or_gt_of_ne ht with h | h
      · simp [kammlerG, heaviside, not_le.2 h]
      · have hxt : ¬ (0 ≤ x - t) := by simp only [not_le]; linarith
        simp [kammlerU, heaviside, hxt]
    rw [hzero]
    rcases eq_or_lt_of_le hx with h | h
    · simp [kammlerG, h]
    · simp [kammlerG, heaviside, not_le.2 h]
  · have _hfac : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hfun : (fun t : ℝ => kammlerG α n t * kammlerU α (x - t))
        = Set.indicator (Icc 0 x) (fun t : ℝ => ((Real.exp (-α * x) * (t ^ n / n !) : ℝ) : ℂ)) := by
      funext t
      by_cases ht : t ∈ Icc (0 : ℝ) x
      · rw [Set.indicator_of_mem ht]
        obtain ⟨h0, h1⟩ := ht
        have h2 : (0 : ℝ) ≤ x - t := by linarith
        simp only [kammlerG, kammlerU, heaviside]
        rw [if_pos h0, if_pos h2]
        push_cast
        rw [show (-(α : ℂ) * (x : ℂ)) = (-(α : ℂ) * (t : ℂ)) + (-(α : ℂ) * ((x : ℂ) - (t : ℂ))) by
          ring, Complex.exp_add]
        ring
      · rw [Set.indicator_of_notMem ht]
        simp only [Set.mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · simp [kammlerG, heaviside, not_le.2 h]
        · have hxt : ¬ (0 ≤ x - t) := by simp only [not_le]; linarith
          simp [kammlerU, heaviside, hxt]
    rw [kammlerConv, hfun, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.le,
      intervalIntegral.integral_ofReal]
    have hrw : ∀ t : ℝ, Real.exp (-α * x) * (t ^ n / n !) = (Real.exp (-α * x) / n !) * t ^ n := by
      intro t; ring
    simp_rw [hrw]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [kammlerG, heaviside]
    rw [if_pos hx.le]
    simp only [Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero n)]
    field_simp
    ring

lemma kammlerUPow_eq (α : ℝ) : ∀ n : ℕ, kammlerUPow α (n + 1) = kammlerG α n := by
  intro n
  induction n with
  | zero => funext x; simp [kammlerUPow, kammlerU, kammlerG]
  | succ n ih =>
      show kammlerConv (kammlerUPow α (n + 1)) (kammlerU α) = kammlerG α (n + 1)
      rw [ih, kammler_conv_step]

lemma kammler_fourier_G {α : ℝ} (hα : 0 < α) (n : ℕ) (s : ℝ) :
    kammlerFourier (kammlerG α n) s
      = (((α : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ)) ^ (n + 1))⁻¹ := by
  set b : ℂ := (α : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ) with hbdef
  have hbre : b.re = α := by simp [hbdef, Complex.add_re, Complex.mul_re]
  have hb : 0 < b.re := by rw [hbre]; exact hα
  have _hfac : ((n ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hfun : (fun x : ℝ => kammlerG α n x * Complex.exp (-2 * Real.pi * Complex.I * (s : ℂ) * x))
      = Set.indicator (Ici 0)
          (fun x : ℝ => ((n ! : ℂ))⁻¹ * ((x : ℂ) ^ n * Complex.exp (-(b * x)))) := by
    funext x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      simp only [kammlerG, heaviside]
      rw [if_pos (Set.mem_Ici.1 hx)]
      push_cast
      rw [show (-(b * (x : ℂ)))
            = (-(α : ℂ) * (x : ℂ)) + (-2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * (x : ℂ)) by
        rw [hbdef]; ring, Complex.exp_add]
      field_simp
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_Ici, not_le] at hx
      simp [kammlerG, heaviside, not_le.2 hx]
  rw [kammlerFourier, hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, kammler_integral_pow_exp hb n]
  field_simp

end KammlerAux

/-- **Fourier transform of the convolution powers of `u(x) = e^{-αx} h(x)`.**

For `α > 0`, the Fourier transform of `u₁ = u` is `(α + 2πis)⁻¹`, and the `n+1`-fold convolution
power `u_{n+1} = u * ⋯ * u` has Fourier transform `(α + 2πis)^{-(n+1)}`. -/
theorem kammler_22
    (α : ℝ) (hα : 0 < α) :
    (kammlerFourier (kammlerUPow α 1)
      = fun s : ℝ => ((α : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ))⁻¹)
    ∧
    (∀ n : ℕ,
      kammlerFourier (kammlerUPow α (n + 1))
        = fun s : ℝ =>
            (((α : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ)) ^ (n + 1))⁻¹) := by
  have key : ∀ n : ℕ, kammlerFourier (kammlerUPow α (n + 1))
      = fun s : ℝ => (((α : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ)) ^ (n + 1))⁻¹ := by
    intro n
    funext s
    rw [kammlerUPow_eq α n, kammler_fourier_G hα n s]
  refine ⟨?_, key⟩
  have h0 := key 0
  simpa using h0
