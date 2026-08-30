import Mathlib

/-!
# The harmonic oscillator `L = -d²/dx² + x²` satisfies `(Lf, f) ≥ (f, f)`

This file formalizes the statement (Stein–Shakarchi, Fourier Analysis, Chapter 4, Problem 9 /
Exercise 18) that for the operator `L = -d²/dx² + x²` acting on Schwartz functions one has
`(Lf, f) ≥ (f, f)`, where `(f, g) = ∫ f * conj g`.

The proof is a form of the Heisenberg uncertainty principle: pointwise one has the identity

`Re ((Lf)(x) * conj (f x)) - ‖f x‖ ^ 2 = ‖x * f x + f' x‖ ^ 2 - B'(x)`

where `B x = Re ((x * f x + f' x) * conj (f x))` is a boundary term. Integrating and showing
that the boundary term does not contribute yields the result.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable def steinHO (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  - deriv (deriv f) x + (x ^ 2) * f x

noncomputable def steinInner (f g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, f x * star (g x)

/-- The boundary term `x * ‖f x‖ ^ 2 + Re (f' x * conj (f x))`. -/
noncomputable def steinBdry (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (((x : ℂ) * f x + deriv f x) * star (f x)).re

/-- The pointwise gap `Re ((Lf)(x) * conj (f x)) - ‖f x‖ ^ 2`. -/
noncomputable def steinGap (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (steinHO f x * star (f x)).re - ‖f x‖ ^ 2

section Pointwise

variable {f : ℝ → ℂ}

lemma contDiff_one_deriv (hC2 : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  have h : ContDiff ℝ (1 + 1 : ℕ) f := by norm_num; exact hC2
  rw [show ((1 + 1 : ℕ) : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num] at h
  exact (contDiff_succ_iff_deriv.mp h).2.2

lemma hasDerivAt_self_of_contDiff (hC2 : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hC2.differentiable (by norm_num) x).hasDerivAt

lemma hasDerivAt_deriv_of_contDiff (hC2 : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  ((contDiff_one_deriv hC2).differentiable one_ne_zero x).hasDerivAt

lemma continuous_deriv_deriv_of_contDiff (hC2 : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have h : ContDiff ℝ ((0 : ℕ∞) + 1) (deriv f) := by simpa using contDiff_one_deriv hC2
  exact ((contDiff_succ_iff_deriv.mp h).2.2).continuous

/-- The algebraic core of the pointwise identity. -/
lemma stein_pointwise_algebra (x : ℝ) (a b c : ℂ) :
    (((1 : ℂ) * a + (x : ℂ) * b + c) * star a + ((x : ℂ) * a + b) * star b).re
      = ‖(x : ℂ) * a + b‖ ^ 2 - (((-c + (x : ℂ) ^ 2 * a) * star a).re - ‖a‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- The key pointwise identity: the derivative of the boundary term. -/
lemma steinBdry_hasDerivAt (hC2 : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (steinBdry f) (‖(x : ℂ) * f x + deriv f x‖ ^ 2 - steinGap f x) x := by
  have hd1 := hasDerivAt_self_of_contDiff hC2
  have hd2 := hasDerivAt_deriv_of_contDiff hC2
  have hcoe : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hA : HasDerivAt (fun y : ℝ => (y : ℂ) * f y + deriv f y)
      (1 * f x + (x : ℂ) * deriv f x + deriv (deriv f) x) x := (hcoe.mul (hd1 x)).add (hd2 x)
  have hGc : HasDerivAt (fun y : ℝ => ((y : ℂ) * f y + deriv f y) * star (f y))
      ((1 * f x + (x : ℂ) * deriv f x + deriv (deriv f) x) * star (f x)
        + ((x : ℂ) * f x + deriv f x) * star (deriv f x)) x :=
    hA.mul ((hd1 x).star)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hGc
  have halg := stein_pointwise_algebra x (f x) (deriv f x) (deriv (deriv f) x)
  have heq : (((1 : ℂ) * f x + (x : ℂ) * deriv f x + deriv (deriv f) x) * star (f x)
        + ((x : ℂ) * f x + deriv f x) * star (deriv f x)).re
      = ‖(x : ℂ) * f x + deriv f x‖ ^ 2 - steinGap f x := by
    rw [halg]
    simp [steinGap, steinHO]
  exact heq ▸ h

lemma continuous_steinGap (hC2 : ContDiff ℝ 2 f) : Continuous (steinGap f) := by
  have _h0 : Continuous f := hC2.continuous
  have _h1 : Continuous (deriv f) := (contDiff_one_deriv hC2).continuous
  have _h2 : Continuous (deriv (deriv f)) := continuous_deriv_deriv_of_contDiff hC2
  unfold steinGap steinHO
  fun_prop

lemma continuous_steinBdryDeriv (hC2 : ContDiff ℝ 2 f) :
    Continuous (fun x : ℝ => ‖(x : ℂ) * f x + deriv f x‖ ^ 2 - steinGap f x) := by
  have _h0 : Continuous f := hC2.continuous
  have _h1 : Continuous (deriv f) := (contDiff_one_deriv hC2).continuous
  have _h2 : Continuous (deriv (deriv f)) := continuous_deriv_deriv_of_contDiff hC2
  unfold steinGap steinHO
  fun_prop

/-- Integrated form of the pointwise identity on `[a, b]`. -/
lemma steinGap_intervalIntegral (hC2 : ContDiff ℝ 2 f) (a b : ℝ) :
    (∫ x in a..b, steinGap f x)
      = (∫ x in a..b, ‖(x : ℂ) * f x + deriv f x‖ ^ 2) - (steinBdry f b - steinBdry f a) := by
  have _h0 : Continuous f := hC2.continuous
  have _h1 : Continuous (deriv f) := (contDiff_one_deriv hC2).continuous
  have hcA : Continuous (fun x : ℝ => ‖(x : ℂ) * f x + deriv f x‖ ^ 2) := by fun_prop
  have hcG : Continuous (steinGap f) := continuous_steinGap hC2
  have key : (∫ x in a..b, (‖(x : ℂ) * f x + deriv f x‖ ^ 2 - steinGap f x))
      = steinBdry f b - steinBdry f a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => steinBdry_hasDerivAt hC2 x) ?_
    exact (continuous_steinBdryDeriv hC2).intervalIntegrable a b
  rw [intervalIntegral.integral_sub (hcA.intervalIntegrable a b)
    (hcG.intervalIntegrable a b)] at key
  linarith [key]

lemma steinGap_intervalIntegral_ge (hC2 : ContDiff ℝ 2 f) {a b : ℝ} (hab : a ≤ b) :
    -(steinBdry f b - steinBdry f a) ≤ ∫ x in a..b, steinGap f x := by
  have _hnn : (0 : ℝ) ≤ ∫ x in a..b, ‖(x : ℂ) * f x + deriv f x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  rw [steinGap_intervalIntegral hC2 a b]
  linarith

end Pointwise

section Decay

/-- If a differentiable function `g`, integrable on `(0, ∞)`, satisfies `g'/2 + x * g ≥ c > 0`
for all large `x`, we get a contradiction: the differential inequality forces `g x ≥ c / (2 x)`
eventually, which is not integrable. -/
lemma no_eventual_positive_bdry
    (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hint : IntegrableOn g (Ioi (0 : ℝ)) volume)
    (c : ℝ) (hc : 0 < c) (x₀ : ℝ) (hx₀ : 1 ≤ x₀)
    (H : ∀ x, x₀ ≤ x → c ≤ g' x / 2 + x * g x) : False := by
  set ψ : ℝ → ℝ := fun y => Real.exp (y ^ 2) * (g y - c / (2 * y)) - c * y with hψdef
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt ψ
      (Real.exp (x ^ 2) * (2 * x) * (g x - c / (2 * x))
        + Real.exp (x ^ 2) * (g' x + c / (2 * x ^ 2)) - c) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa [mul_comm] using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (y ^ 2)) (Real.exp (x ^ 2) * (2 * x)) x :=
      (Real.hasDerivAt_exp (x ^ 2)).comp_hasDerivAt x h1
    have h3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h4 : HasDerivAt (fun y : ℝ => c / (2 * y)) (-(c / (2 * x ^ 2))) x := by
      have h := (hasDerivAt_const x c).div h3 (by positivity)
      have hval : -(c * 2) / (2 * x) ^ 2 = -(c / (2 * x ^ 2)) := by
        have hx0 : x ≠ 0 := ne_of_gt hx
        ring_nf
        rw [mul_assoc]
      exact hval ▸ h
    have h5 : HasDerivAt (fun y : ℝ => g y - c / (2 * y)) (g' x + c / (2 * x ^ 2)) x := by
      have hd := (hg x).sub h4
      have hval : g' x - -(c / (2 * x ^ 2)) = g' x + c / (2 * x ^ 2) := by ring
      exact hval ▸ hd
    have h6 : HasDerivAt (fun y : ℝ => c * y) c x := by simpa using (hasDerivAt_id x).const_mul c
    exact (h2.mul h5).sub h6
  have hpos : (0 : ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hdnn : ∀ x, x₀ ≤ x → 0 ≤ deriv ψ x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hpos hx
    rw [(hderiv x hx0).deriv]
    have _hH := H x hx
    have _hexp : (1 : ℝ) ≤ Real.exp (x ^ 2) := Real.one_le_exp (by positivity)
    have _hkey : c ≤ Real.exp (x ^ 2) * (2 * x) * (g x - c / (2 * x))
        + Real.exp (x ^ 2) * (g' x + c / (2 * x ^ 2)) := by
      have expand : Real.exp (x ^ 2) * (2 * x) * (g x - c / (2 * x))
          + Real.exp (x ^ 2) * (g' x + c / (2 * x ^ 2))
          = Real.exp (x ^ 2) * (2 * x * g x + g' x - c + c / (2 * x ^ 2)) := by
        field_simp; ring
      rw [expand]
      have _h1 : 2 * c ≤ 2 * x * g x + g' x := by linarith
      have _h2 : (0 : ℝ) ≤ c / (2 * x ^ 2) := by positivity
      have _h3 : c ≤ 2 * x * g x + g' x - c + c / (2 * x ^ 2) := by linarith
      nlinarith [Real.exp_pos (x ^ 2)]
    linarith
  have hmono : MonotoneOn ψ (Ici x₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x₀)
    · intro x hx
      exact ((hderiv x (lt_of_lt_of_le hpos hx)).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact ((hderiv x (lt_trans hpos hx)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact hdnn x (le_of_lt hx)
  set X := x₀ + |ψ x₀| / c + 1 with hXdef
  have hXge : x₀ ≤ X := by
    have : (0 : ℝ) ≤ |ψ x₀| / c := by positivity
    simp only [hXdef]; linarith
  have hgbd : ∀ x, X ≤ x → c / (2 * x) ≤ g x := by
    intro x hx
    have hx0 : x₀ ≤ x := le_trans hXge hx
    have hmm := hmono Set.self_mem_Ici (mem_Ici.mpr hx0) hx0
    have _hxx : |ψ x₀| ≤ c * (x - x₀) := by
      have h1 : |ψ x₀| / c + 1 ≤ x - x₀ := by simp only [hXdef] at hx; linarith
      have _h2 := (div_le_iff₀ hc).mp (by linarith : |ψ x₀| / c ≤ x - x₀)
      linarith
    have _h1 : 0 ≤ Real.exp (x ^ 2) * (g x - c / (2 * x)) := by
      have hle : ψ x₀ ≤ ψ x := hmm
      simp only [hψdef] at hle
      have habs : -|ψ x₀| ≤ ψ x₀ := neg_abs_le _
      simp only [hψdef] at habs
      nlinarith [Real.exp_pos (x ^ 2)]
    have _hexp : 0 < Real.exp (x ^ 2) := Real.exp_pos _
    nlinarith
  have hXpos : 0 < X := lt_of_lt_of_le hpos hXge
  have hIntg : IntegrableOn g (Ioi X) volume :=
    hint.mono_set (Ioi_subset_Ioi (le_of_lt hXpos))
  have hInth : IntegrableOn (fun x : ℝ => c / (2 * x)) (Ioi X) volume := by
    refine MeasureTheory.Integrable.mono' hIntg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have _hx0 : 0 < x := lt_trans hXpos hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hgbd x (le_of_lt hx)
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi X) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun (hInth.const_mul (2 / c)) ?_ measurableSet_Ioi
    intro x hx
    have _hx0 : 0 < x := lt_trans hXpos hx
    field_simp
  exact not_integrableOn_Ioi_inv hinv

end Decay

section Main

variable {f : ℝ → ℂ}

lemma sq_norm_hasDerivAt (hC2 : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (fun y => ‖f y‖ ^ 2) (2 * (deriv f x * star (f x)).re) x := by
  have hd1 := hasDerivAt_self_of_contDiff hC2
  have hGc : HasDerivAt (fun y : ℝ => f y * star (f y))
      (deriv f x * star (f x) + f x * star (deriv f x)) x := (hd1 x).mul ((hd1 x).star)
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hGc
  have heq : (fun y : ℝ => ‖f y‖ ^ 2)
      = fun y : ℝ => (Complex.reCLM ∘ fun y : ℝ => f y * star (f y)) y := by
    funext y
    simp [Complex.mul_conj, Complex.sq_norm]
  rw [heq]
  have halg : (deriv f x * star (f x) + f x * star (deriv f x)).re
      = 2 * (deriv f x * star (f x)).re := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  exact halg ▸ h

lemma steinBdry_eq (f : ℝ → ℂ) (x : ℝ) :
    steinBdry f x = (2 * (deriv f x * star (f x)).re) / 2 + x * ‖f x‖ ^ 2 := by
  simp [steinBdry, Complex.add_re, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma integrable_sq_norm (h_int_ff : Integrable (fun x : ℝ => f x * star (f x)) volume) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume := by
  refine h_int_ff.re.congr ?_
  filter_upwards with x
  simp [Complex.mul_conj, Complex.sq_norm]

/-- There are arbitrarily large `x` where the boundary term is at most `ε`. -/
lemma exists_large_steinBdry_le (hC2 : ContDiff ℝ 2 f)
    (h_int_ff : Integrable (fun x : ℝ => f x * star (f x)) volume)
    {ε : ℝ} (hε : 0 < ε) (b : ℝ) : ∃ x, b ≤ x ∧ steinBdry f x ≤ ε := by
  by_contra! hcon
  refine no_eventual_positive_bdry (fun y => ‖f y‖ ^ 2)
    (fun y => 2 * (deriv f y * star (f y)).re) (sq_norm_hasDerivAt hC2)
    (integrable_sq_norm h_int_ff).integrableOn ε hε (max b 1) (le_max_right _ _) ?_
  intro x hx
  have hxb : b ≤ x := le_trans (le_max_left _ _) hx
  have h := hcon x hxb
  rw [steinBdry_eq] at h
  linarith

/-- There are arbitrarily negative `x` where the boundary term is at least `-ε`. -/
lemma exists_small_steinBdry_ge (hC2 : ContDiff ℝ 2 f)
    (h_int_ff : Integrable (fun x : ℝ => f x * star (f x)) volume)
    {ε : ℝ} (hε : 0 < ε) (b : ℝ) : ∃ x, x ≤ b ∧ -ε ≤ steinBdry f x := by
  by_contra! hcon
  have hd_comp : ∀ x, HasDerivAt (fun y => ‖f (-y)‖ ^ 2)
      (-(2 * (deriv f (-x) * star (f (-x))).re)) x := by
    intro x
    have h := (sq_norm_hasDerivAt hC2 (-x)).comp_hasDerivAt x (hasDerivAt_neg x)
    simpa [mul_comm] using h
  refine no_eventual_positive_bdry (fun y => ‖f (-y)‖ ^ 2)
    (fun y => -(2 * (deriv f (-y) * star (f (-y))).re)) hd_comp ?_ ε hε (max (-b) 1)
    (le_max_right _ _) ?_
  · exact ((integrable_sq_norm h_int_ff).comp_neg).integrableOn
  · intro x hx
    have hxb : -x ≤ b := by
      have : -b ≤ x := le_trans (le_max_left _ _) hx
      linarith
    have h := hcon (-x) hxb
    rw [steinBdry_eq] at h
    push_cast at h ⊢
    nlinarith [h]

lemma integrable_steinGap
    (h_int_HOf : Integrable (fun x : ℝ => steinHO f x * star (f x)) volume)
    (h_int_ff : Integrable (fun x : ℝ => f x * star (f x)) volume) :
    Integrable (steinGap f) volume := by
  have h1 : Integrable (fun x : ℝ => (steinHO f x * star (f x)).re) volume := by
    refine h_int_HOf.re.congr ?_
    filter_upwards with x
    simp
  exact h1.sub (integrable_sq_norm h_int_ff)

lemma integral_steinGap_nonneg (hC2 : ContDiff ℝ 2 f)
    (h_int_HOf : Integrable (fun x : ℝ => steinHO f x * star (f x)) volume)
    (h_int_ff : Integrable (fun x : ℝ => f x * star (f x)) volume) :
    0 ≤ ∫ x : ℝ, steinGap f x := by
  have hgap := integrable_steinGap h_int_HOf h_int_ff
  choose R hR1 hR2 using fun n : ℕ =>
    exists_large_steinBdry_le hC2 h_int_ff (ε := 1 / ((n : ℝ) + 1)) (by positivity) (n : ℝ)
  choose S hS1 hS2 using fun n : ℕ =>
    exists_small_steinBdry_ge hC2 h_int_ff (ε := 1 / ((n : ℝ) + 1)) (by positivity) (-(n : ℝ))
  have hRtop : Tendsto R atTop atTop := tendsto_atTop_mono hR1 tendsto_natCast_atTop_atTop
  have hSbot : Tendsto S atTop atBot :=
    tendsto_atBot_mono hS1 (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hconv := MeasureTheory.intervalIntegral_tendsto_integral hgap hSbot hRtop
  have hlow : Tendsto (fun n : ℕ => -(2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      h.inv_tendsto_atTop.congr (fun _ => by simp)
    simpa using (h2.const_mul (2 : ℝ)).neg
  refine le_of_tendsto_of_tendsto' hlow hconv (fun n => ?_)
  have hle : S n ≤ R n := by
    have h1 : S n ≤ -(n : ℝ) := hS1 n
    have h2 : (n : ℝ) ≤ R n := hR1 n
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have _h4 := steinGap_intervalIntegral_ge hC2 hle
  have _hb1 := hR2 n
  have _hb2 := hS2 n
  linarith

/-- **The harmonic oscillator inequality**: for `L = -d²/dx² + x²` one has `(Lf, f) ≥ (f, f)`. -/
theorem stein_18
    (f : ℝ → ℂ)
    (hC2 : ContDiff ℝ 2 f)
    (h_int_HOf :
      MeasureTheory.Integrable (fun x : ℝ => steinHO f x * star (f x)) volume)
    (h_int_ff :
      MeasureTheory.Integrable (fun x : ℝ => f x * star (f x)) volume) :
    (steinInner (steinHO f) f).re ≥ (steinInner f f).re := by
  have hsq := integrable_sq_norm h_int_ff
  have hHOre : Integrable (fun x : ℝ => (steinHO f x * star (f x)).re) volume := by
    refine h_int_HOf.re.congr ?_
    filter_upwards with x
    simp
  have h1 : (steinInner (steinHO f) f).re = ∫ x : ℝ, (steinHO f x * star (f x)).re := by
    rw [steinInner, ← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ h_int_HOf]
    rfl
  have h2 : (steinInner f f).re = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [steinInner, ← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ h_int_ff]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [Complex.mul_conj, Complex.sq_norm]
  have h3 : (∫ x : ℝ, steinGap f x)
      = (∫ x : ℝ, (steinHO f x * star (f x)).re) - ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [← MeasureTheory.integral_sub hHOre hsq]
    rfl
  have h4 := integral_steinGap_nonneg hC2 h_int_HOf h_int_ff
  rw [h1, h2, ge_iff_le, ← sub_nonneg, ← h3]
  exact h4

end Main

section Schwartz

/-- Every Schwartz function is bounded. -/
lemma SchwartzMap.exists_norm_le (f : SchwartzMap ℝ ℂ) : ∃ B, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨C, _, h⟩ := f.decay 0 0
  exact ⟨C, fun x => by simpa using h x⟩

lemma integrable_schwartz_mul_star (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ⇑f x * star (⇑f x)) volume := by
  obtain ⟨B, hB⟩ := f.exists_norm_le
  have hdom : Integrable (fun x : ℝ => B * ‖f x‖) volume := (f.integrable.norm).const_mul B
  refine Integrable.mono' hdom
    ((f.continuous.mul (continuous_star.comp f.continuous)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, norm_star]
  nlinarith [norm_nonneg (f x), hB x]

lemma integrable_steinHO_schwartz (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => steinHO (⇑f) x * star (⇑f x)) volume := by
  set g : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ f) with hg
  have hfd : ⇑(SchwartzMap.derivCLM ℝ ℂ f) = deriv ⇑f :=
    funext fun y => SchwartzMap.derivCLM_apply ℝ f y
  have hgx : ∀ x, deriv (deriv ⇑f) x = g x := by
    intro x
    rw [hg, SchwartzMap.derivCLM_apply, hfd]
  obtain ⟨B, hB⟩ := f.exists_norm_le
  have _hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hdom : Integrable (fun x : ℝ => B * (‖g x‖ + ‖x‖ ^ 2 * ‖f x‖)) volume :=
    ((g.integrable.norm).add (SchwartzMap.integrable_pow_mul volume f 2)).const_mul B
  refine Integrable.mono' hdom ?_ ?_
  · have hs : Continuous (fun x : ℝ => steinHO (⇑f) x) := by
      unfold steinHO
      have _hdd : Continuous (deriv (deriv ⇑f)) := by
        simp only [funext hgx]; exact g.continuous
      fun_prop
    exact (hs.mul (continuous_star.comp f.continuous)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, norm_star]
    have _h1 : ‖steinHO (⇑f) x‖ ≤ ‖g x‖ + ‖x‖ ^ 2 * ‖f x‖ := by
      unfold steinHO
      calc ‖-deriv (deriv ⇑f) x + (x : ℂ) ^ 2 * f x‖
          ≤ ‖-deriv (deriv ⇑f) x‖ + ‖(x : ℂ) ^ 2 * f x‖ := norm_add_le _ _
        _ = ‖g x‖ + ‖x‖ ^ 2 * ‖f x‖ := by
            rw [norm_neg, hgx, norm_mul, norm_pow, Complex.norm_real]
    have _h3 : 0 ≤ ‖g x‖ + ‖x‖ ^ 2 * ‖f x‖ := by positivity
    nlinarith [norm_nonneg (f x), hB x]

/-- **Stein–Shakarchi, Fourier Analysis, Chapter 4, Problem 9** (Schwartz version):
for the harmonic oscillator `L = -d²/dx² + x²` and every Schwartz function `f`,
`(L f, f) ≥ (f, f)`. -/
theorem stein_18_schwartz (f : SchwartzMap ℝ ℂ) :
    (steinInner (steinHO ⇑f) ⇑f).re ≥ (steinInner ⇑f ⇑f).re :=
  stein_18 ⇑f (f.smooth 2) (integrable_steinHO_schwartz f) (integrable_schwartz_mul_star f)

end Schwartz
