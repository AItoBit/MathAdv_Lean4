import Mathlib

/-!
# Plancherel identity for a truncated Fourier approximation

Let `F` be an integrable, square-integrable function on `ℝ`, let `Y` be integrable and
square-integrable on a finite interval `[a,b]`, and set

* `f (x) = ∫ s, F s * exp (2πi s x)`,
* `y (x) = ∫ s in a..b, Y s * exp (2πi s x)`.

Then
`∫ |f - y|² = ∫ |f|² - ∫_a^b |F|² + ∫_a^b |F - Y|²`.

The proof is an application of the Plancherel identity: `f - y` is the (inverse) Fourier
transform of `G = F - 1_{(a,b]} Y`, so `∫ |f - y|² = ∫ |G|²`, and the right-hand side is
obtained by splitting `∫ |G|²` over `(a,b]` and its complement.

Since Mathlib only provides Plancherel's theorem in the abstract `L²` form (as an isometry of
`L²`) and for Schwartz functions, the first part of this file establishes the concrete
Plancherel identity `∫ ‖𝓕 f‖² = ∫ ‖f‖²` for functions in `L¹ ∩ L²`.
-/

open MeasureTheory FourierTransform SchwartzMap Complex

noncomputable section

namespace Kammler21

/-! ### Plancherel's theorem for `L¹ ∩ L²` functions -/

/-- The squared norm of an `L²` function is the integral of the squared pointwise norms. -/
lemma norm_sq_Lp_two (u : Lp ℂ 2 (volume : Measure ℝ)) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have h1 : (‖u‖ : ℝ) ^ 2 = RCLike.re (inner ℂ u u) := by
    rw [← @inner_self_eq_norm_sq ℂ]
  rw [h1, L2.inner_def]
  have h2 : ∀ a : ℝ, inner ℂ ((u : ℝ → ℂ) a) ((u : ℝ → ℂ) a) = ((‖(u : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp only [h2]
  rw [integral_complex_ofReal]
  simp

/-- For an integrable function, the classical Fourier transform is continuous. -/
lemma continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (by fun_prop)
    (IsModuleTopology.continuous_bilinear_of_finite_left (innerₗ ℝ)) hf

/-- The multiplication formula (self-adjointness of the Fourier transform), in the form needed
below. -/
lemma integral_smul_fourier {f : ℝ → ℂ} (hf : Integrable f) {g : ℝ → ℝ}
    (hgi : Integrable (fun y => ((g y : ℂ)))) :
    ∫ x, g x • 𝓕 f x = ∫ x, (𝓕 (fun y => ((g y : ℂ))) x) • f x := by
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    (V := ℝ) (W := ℝ) (f := f) (g := fun y => ((g y : ℂ)))
    Real.continuous_fourierChar continuous_inner hf hgi
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    show inner ℝ y x = inner ℝ x y
    exact real_inner_comm _ _
  rw [hflip] at key
  have e1 : ∀ x : ℝ, g x • 𝓕 f x
      = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f x • ((g x : ℂ)) := by
    intro x
    show g x • 𝓕 f x = 𝓕 f x • ((g x : ℂ))
    simp [Complex.real_smul, smul_eq_mul]; ring
  have e2 : ∀ x : ℝ, (𝓕 (fun y => ((g y : ℂ))) x) • f x
      = f x • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (fun y => ((g y : ℂ))) x := by
    intro x
    show _ • f x = f x • 𝓕 (fun y => ((g y : ℂ))) x
    simp [smul_eq_mul]; ring
  simp only [e1, e2]
  exact key

/-- The abstract `L²`-Fourier transform of an `L¹ ∩ L²` function is represented by the classical
Fourier integral. -/
lemma coeFn_fourier_toLp {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2 volume) :
    ((𝓕 (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable one_le_two
  · exact (continuous_fourier h1).locallyIntegrable
  · intro g hg hgc
    set G : 𝓢(ℝ, ℂ) := HasCompactSupport.toSchwartzMap (f := fun x => (g x : ℂ))
      (by exact hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
      (by exact Complex.ofRealCLM.contDiff.comp hg) with hG
    have hGf : ∀ x, G x = (g x : ℂ) := fun _ => rfl
    have hL : ∫ x, g x • ((𝓕 (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) x
        = (Lp.toTemperedDistribution (𝓕 (h2.toLp f))) G := by
      rw [Lp.toTemperedDistribution_apply]
      simp [hGf, Complex.real_smul]
    have hstep : (Lp.toTemperedDistribution (𝓕 (h2.toLp f))) G
        = ∫ x, (𝓕 (fun y => ((g y : ℂ))) x) • f x := by
      rw [← Lp.fourier_toTemperedDistribution_eq (h2.toLp f),
        TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      have hco : ∀ x, (𝓕 G) x = 𝓕 (fun y => ((g y : ℂ))) x := by
        intro x; rw [SchwartzMap.fourier_coe]; rfl
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx, hco x]
    rw [hL, hstep, integral_smul_fourier h1 (G.integrable (μ := volume))]

/-- Plancherel's identity for a function in `L¹ ∩ L²`. -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2 volume) :
    ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hae := coeFn_fourier_toLp h1 h2
  have e1 : ∫ x, ‖𝓕 f x‖ ^ 2 = ‖(𝓕 (h2.toLp f) : Lp ℂ 2 volume)‖ ^ 2 := by
    rw [norm_sq_Lp_two]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have e2 : ∫ x, ‖f x‖ ^ 2 = ‖h2.toLp f‖ ^ 2 := by
    rw [norm_sq_Lp_two]
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [e1, e2, Lp.norm_fourier_eq]

/-- Plancherel's identity for the inverse Fourier transform of a function in `L¹ ∩ L²`. -/
theorem integral_norm_sq_fourierInv {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2 volume) :
    ∫ x, ‖𝓕⁻ f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have : ∀ x : ℝ, ‖𝓕⁻ f x‖ ^ 2 = ‖𝓕 f (-x)‖ ^ 2 := by
    intro x; rw [Real.fourierInv_eq_fourier_neg]
  simp only [this]
  rw [integral_neg_eq_self (fun x : ℝ => ‖𝓕 f x‖ ^ 2) volume]
  exact integral_norm_sq_fourier h1 h2

/-! ### The main statement -/

/-- The transform `x ↦ ∫ s, H s * exp (2πi s x)` is the inverse Fourier transform. -/
lemma transform_eq_fourierInv (H : ℝ → ℂ) (x : ℝ) :
    (∫ s, H s * Complex.exp (2 * Real.pi * Complex.I * s * x)) = 𝓕⁻ H x := by
  rw [Real.fourierInv_eq']
  congr 1
  ext s
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  simp [RCLike.inner_apply]
  ring

/-- Multiplying an integrable function by a unimodular exponential keeps it integrable. -/
lemma integrable_mul_exp {H : ℝ → ℂ} (h : Integrable H) (x : ℝ) :
    Integrable (fun s : ℝ => H s * Complex.exp (2 * Real.pi * Complex.I * s * x)) := by
  apply Integrable.mono' h.norm
  · exact h.aestronglyMeasurable.mul (by fun_prop)
  · filter_upwards with s
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I * s * x).re = 0 := by simp
    rw [hre]
    simp

/-- Splitting the `L²` mass of `F - 1_{(a,b]} Y` over `(a,b]` and its complement. -/
lemma integral_norm_sq_sub_indicator (F Y : ℝ → ℂ) (a b : ℝ)
    (hF : Integrable fun x => ‖F x‖ ^ 2)
    (hG : Integrable fun x => ‖F x - Set.indicator (Set.Ioc a b) Y x‖ ^ 2) :
    ∫ x, ‖F x - Set.indicator (Set.Ioc a b) Y x‖ ^ 2
      = (∫ x, ‖F x‖ ^ 2) - (∫ x in Set.Ioc a b, ‖F x‖ ^ 2)
        + ∫ x in Set.Ioc a b, ‖F x - Y x‖ ^ 2 := by
  have hS : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  rw [← integral_add_compl hS hF, ← integral_add_compl hS hG]
  have h1 : ∫ x in (Set.Ioc a b)ᶜ, ‖F x - Set.indicator (Set.Ioc a b) Y x‖ ^ 2
      = ∫ x in (Set.Ioc a b)ᶜ, ‖F x‖ ^ 2 := by
    refine setIntegral_congr_fun hS.compl fun x hx => ?_
    dsimp only
    rw [Set.indicator_of_notMem hx]
    simp
  have h2 : ∫ x in Set.Ioc a b, ‖F x - Set.indicator (Set.Ioc a b) Y x‖ ^ 2
      = ∫ x in Set.Ioc a b, ‖F x - Y x‖ ^ 2 := by
    refine setIntegral_congr_fun hS fun x hx => ?_
    dsimp only
    rw [Set.indicator_of_mem hx]
  rw [h1, h2]
  ring

/-- **Main result.**  For `F` integrable and square-integrable on `ℝ`, and `Y` integrable and
square-integrable on `(a,b]`, writing
`f (x) = ∫ s, F s exp (2πi s x)`, `y (x) = ∫_a^b Y s exp (2πi s x)`, one has
`∫ |f - y|² = ∫ |f|² - ∫_a^b |F|² + ∫_a^b |F - Y|²`. -/
theorem kammler_21 (F Y : ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    (hY1 : IntegrableOn Y (Set.Ioc a b)) (hY2 : MemLp Y 2 (volume.restrict (Set.Ioc a b))) :
    let fourier_full (F : ℝ → ℂ) (x : ℝ) : ℂ :=
      ∫ s, F s * Complex.exp (2 * Real.pi * Complex.I * s * x)
    let fourier_on (F : ℝ → ℂ) (a b : ℝ) (x : ℝ) : ℂ :=
      ∫ s in a..b, F s * Complex.exp (2 * Real.pi * Complex.I * s * x)
    ∫ x, ‖fourier_full F x - fourier_on Y a b x‖ ^ 2 =
      (∫ x, ‖fourier_full F x‖ ^ 2) - (∫ s in a..b, ‖F s‖ ^ 2)
        + ∫ s in a..b, ‖F s - Y s‖ ^ 2 := by
  intro fourier_full fourier_on
  have hS : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  set IY : ℝ → ℂ := Set.indicator (Set.Ioc a b) Y with hIY
  have hIY1 : Integrable IY := (integrable_indicator_iff hS).2 hY1
  have hIY2 : MemLp IY 2 volume := (memLp_indicator_iff_restrict hS).2 hY2
  set G : ℝ → ℂ := fun s => F s - IY s with hGdef
  have hG1 : Integrable G := hF1.sub hIY1
  have hG2 : MemLp G 2 volume := hF2.sub hIY2
  -- the truncated transform is the transform of the indicator function
  have hon : ∀ x, fourier_on Y a b x
      = ∫ s, IY s * Complex.exp (2 * Real.pi * Complex.I * s * x) := by
    intro x
    show (∫ s in a..b, Y s * Complex.exp (2 * Real.pi * Complex.I * s * x)) = _
    rw [intervalIntegral.integral_of_le hab.le, ← integral_indicator hS]
    congr 1
    ext s
    by_cases hs : s ∈ Set.Ioc a b <;>
      simp [hIY, Set.indicator_of_mem, Set.indicator_of_notMem, hs]
  -- the difference of the two transforms is the transform of `G`
  have hdiff : ∀ x, fourier_full F x - fourier_on Y a b x = 𝓕⁻ G x := by
    intro x
    rw [hon x]
    show (∫ s, F s * Complex.exp (2 * Real.pi * Complex.I * s * x)) - _ = _
    rw [← transform_eq_fourierInv]
    rw [← integral_sub]
    · congr 1
      ext s
      rw [hGdef]
      ring
    · exact integrable_mul_exp hF1 x
    · exact integrable_mul_exp hIY1 x
  have hfull : ∀ x, fourier_full F x = 𝓕⁻ F x := fun x => transform_eq_fourierInv F x
  have hL : (∫ x, ‖fourier_full F x - fourier_on Y a b x‖ ^ 2) = ∫ x, ‖𝓕⁻ G x‖ ^ 2 := by
    simp only [hdiff]
  have hR : (∫ x, ‖fourier_full F x‖ ^ 2) = ∫ x, ‖𝓕⁻ F x‖ ^ 2 := by
    simp only [hfull]
  rw [hL, hR, integral_norm_sq_fourierInv hG1 hG2, integral_norm_sq_fourierInv hF1 hF2]
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  exact integral_norm_sq_sub_indicator F Y a b
    ((memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).1 hF2)
    ((memLp_two_iff_integrable_sq_norm hG2.aestronglyMeasurable).1 hG2)

/-
The statement as originally posed was:

theorem kammler_21 (F Y : ℝ → ℂ) {a b : ℝ} (hab : a < b) :
  let fourier_full (F : ℝ → ℂ) (x : ℝ) : ℂ :=
    ∫ s, F s * Complex.exp (2 * Real.pi * Complex.I * s * x)
  let fourier_on (F : ℝ → ℂ) (a b : ℝ) (x : ℝ) : ℂ :=
    ∫ s in a..b, F s * Complex.exp (2 * Real.pi * Complex.I * s * x)
  ∫ x, ‖fourier_full F x - fourier_on Y a b x‖ ^ 2 =
    ∫ x, ‖fourier_full F x‖ ^ 2 - ∫ s in a..b, ‖F s‖ ^ 2 + ∫ s in a..b, ‖F s - Y s‖ ^ 2

Two changes were made to obtain `Kammler21.kammler_21` above.

* Parenthesisation: in `∫ x, ‖fourier_full F x‖ ^ 2 - ∫ s in a..b, ‖F s‖ ^ 2 + ...` the
  integral binder `∫ x, ...` extends to the end of the expression, so the two constant terms
  end up *inside* the integral over `ℝ`; the resulting function is then not integrable
  (unless the constant vanishes) and the integral collapses to `0` by convention.  The
  intended reading, made explicit above, is
  `(∫ x, ‖f x‖²) - (∫_a^b ‖F‖²) + ∫_a^b ‖F - Y‖²`.
* Hypotheses: the informal statement assumes `F` to be piecewise smooth with small regular
  tails and `Y` piecewise smooth on `[a,b]`.  These are used only to guarantee that all the
  integrals converge, and are replaced here by the exact analytic requirements: `F` is
  integrable and square integrable on `ℝ`, and `Y` is integrable and square integrable on the
  interval.  Without such hypotheses none of the integrals need converge.
-/

end Kammler21
