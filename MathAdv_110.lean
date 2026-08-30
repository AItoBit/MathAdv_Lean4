import Mathlib

/-!
# Orthogonality of band-limited functions (Kammler, Fourier Analysis, Exercise 4.9)

Let `a 1 < b 1 ≤ a 2 < b 2 ≤ ⋯ ≤ a N < b N` and, for `n = 1, …, N`,
`f n x = ∫ s in [a n, b n], F n s * exp (2 π i s x)`, where `F n` is (piecewise smooth,
hence measurable) on `[a n, b n]` with `∫ s in [a n, b n], ‖F n s‖ ^ 2 = 1`.
Then `∫ x : ℝ, f n x * conj (f m x) = if n = m then 1 else 0`.

The proof is the Parseval/Plancherel identity for the Fourier transform: `f n` is the
(inverse) Fourier transform of `F n · 1_[a n, b n]`, and the Fourier transform preserves the
`L²` inner product; the functions `F n · 1_[a n, b n]` have essentially disjoint supports.
-/

open MeasureTheory SchwartzMap FourierTransform Real Complex

noncomputable section

/-! ## Plancherel/Parseval for functions in `L¹ ∩ L²` -/

/-- For `g ∈ L¹ ∩ L²`, the abstract `L²`-Fourier transform of `g` agrees almost everywhere with
the concrete Fourier integral of `g`. -/
theorem coeFn_fourier_toLp_ae_eq (g : ℝ → ℂ) (h1 : Integrable g) (h2 : MemLp g 2 volume) :
    ∀ᵐ x, ((𝓕 (h2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) x = 𝓕 g x := by
  have hcont : Continuous (𝓕 g) := by
    change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g)
    exact VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner h1
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact hcont.locallyIntegrable
  · intro φ hφ hφc
    have hcs : HasCompactSupport (fun x : ℝ => (φ x : ℂ)) :=
      hφc.comp_left Complex.ofReal_zero
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    set Φ : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm with _hΦ
    have hΦx : ∀ x, Φ x = (φ x : ℂ) := fun _ => rfl
    have step1 : ∫ x, Φ x • ((𝓕 (h2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) x
        = ∫ x, (𝓕 Φ) x • g x := by
      rw [← Lp.toTemperedDistribution_apply, ← Lp.fourier_toTemperedDistribution_eq,
        TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      refine integral_congr_ae ?_
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]
    have step2 : ∫ ξ, (𝓕 g ξ) • Φ ξ = ∫ x, g x • (𝓕 Φ) x := by
      have hflip : ∫ ξ, (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g ξ) • (Φ : ℝ → ℂ) ξ
          = ∫ x, g x • (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (Φ : ℝ → ℂ) x) :=
        VectorFourier.integral_fourierIntegral_smul_eq_flip
          continuous_fourierChar continuous_inner h1 Φ.integrable
      simpa [SchwartzMap.coe_fourier] using hflip
    calc ∫ x, φ x • ((𝓕 (h2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) x
        = ∫ x, Φ x • ((𝓕 (h2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) x := by
          simp [hΦx, Complex.real_smul]
      _ = ∫ x, (𝓕 Φ) x • g x := step1
      _ = ∫ x, g x • (𝓕 Φ) x := by simp [smul_eq_mul, mul_comm]
      _ = ∫ ξ, (𝓕 g ξ) • Φ ξ := step2.symm
      _ = ∫ x, φ x • 𝓕 g x := by simp [hΦx, Complex.real_smul, smul_eq_mul, mul_comm]

/-- Parseval's identity for the Fourier transform of functions in `L¹ ∩ L²`. -/
theorem integral_fourier_mul_conj_eq (g h : ℝ → ℂ) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hh1 : Integrable h) (hh2 : MemLp h 2 volume) :
    ∫ x, 𝓕 g x * (starRingEnd ℂ) (𝓕 h x) = ∫ x, g x * (starRingEnd ℂ) (h x) := by
  have key := Lp.inner_fourier_eq (hh2.toLp h) (hg2.toLp g)
  rw [L2.inner_def, L2.inner_def] at key
  have hL : ∫ x, 𝓕 g x * (starRingEnd ℂ) (𝓕 h x)
      = ∫ x, inner ℂ (((𝓕 (hh2.toLp h) : Lp ℂ 2 volume) : ℝ → ℂ) x)
          (((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp_ae_eq g hg1 hg2, coeFn_fourier_toLp_ae_eq h hh1 hh2]
      with x hx hy
    rw [RCLike.inner_apply, hx, hy, mul_comm]
  have hR : ∫ x, g x * (starRingEnd ℂ) (h x)
      = ∫ x, inner ℂ (((hh2.toLp h : Lp ℂ 2 volume) : ℝ → ℂ) x)
          (((hg2.toLp g : Lp ℂ 2 volume) : ℝ → ℂ) x) := by
    refine integral_congr_ae ?_
    filter_upwards [hg2.coeFn_toLp, hh2.coeFn_toLp] with x hx hy
    rw [RCLike.inner_apply, hx, hy, mul_comm]
  rw [hL, hR]
  exact key

/-! ## Integrability of the truncated functions -/

/-- If `∫ s in [a, b], ‖F s‖ ^ 2 = 1` then `F` restricted to `[a, b]` is square integrable. -/
theorem integrableOn_sq_norm_of_integral_eq_one {a b : ℝ} {F : ℝ → ℂ}
    (hnorm : ∫ s in Set.Icc a b, ‖F s‖ ^ (2 : ℕ) = 1) :
    IntegrableOn (fun s => ‖F s‖ ^ (2 : ℕ)) (Set.Icc a b) volume := by
  by_contra hcon
  rw [integral_undef hcon] at hnorm
  exact zero_ne_one hnorm

theorem memLp_two_indicator {a b : ℝ} {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume)
    (hI : IntegrableOn (fun s => ‖F s‖ ^ (2 : ℕ)) (Set.Icc a b) volume) :
    MemLp ((Set.Icc a b).indicator F) 2 volume := by
  have hmeas : AEStronglyMeasurable ((Set.Icc a b).indicator F) volume :=
    hF.indicator measurableSet_Icc
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hEq : (fun x => ‖(Set.Icc a b).indicator F x‖ ^ (2 : ℕ))
      = (Set.Icc a b).indicator (fun s => ‖F s‖ ^ (2 : ℕ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
  rw [hEq, integrable_indicator_iff measurableSet_Icc]
  exact hI

theorem integrable_indicator_of_sq {a b : ℝ} {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume)
    (hI : IntegrableOn (fun s => ‖F s‖ ^ (2 : ℕ)) (Set.Icc a b) volume) :
    Integrable ((Set.Icc a b).indicator F) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  have : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hmem : MemLp F 2 (volume.restrict (Set.Icc a b)) := by
    rw [memLp_two_iff_integrable_sq_norm hF.restrict]
    exact hI
  exact hmem.integrable one_le_two

/-! ## The functions of the exercise -/

/-- `kammler_f a b F n` is the function `f n` of the exercise: the inverse Fourier transform of
`F n`, truncated to the interval `[a n, b n]`. -/
noncomputable def kammler_f
    (a b : ℕ → ℝ) (F : ℕ → ℝ → ℂ)
    (n : ℕ) (x : ℝ) : ℂ :=
  ∫ s : ℝ,
    Set.indicator (Set.Icc (a n) (b n))
      (fun s => F n s * Complex.exp (2 * Real.pi * Complex.I * s * x)) s

/-- `kammler_f` is the Fourier transform of the truncation of `F n`, evaluated at `-x`. -/
theorem kammler_f_eq_fourier (a b : ℕ → ℝ) (F : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) :
    kammler_f a b F n x = 𝓕 ((Set.Icc (a n) (b n)).indicator (F n)) (-x) := by
  rw [← fourierInv_eq_fourier_neg, fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have hinner : (inner ℝ s x : ℝ) = s * x := by simp [RCLike.inner_apply, mul_comm]
  by_cases hs : s ∈ Set.Icc (a n) (b n)
  · simp only [Set.indicator_of_mem hs, hinner, smul_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  · simp [Set.indicator_of_notMem hs]

/-- The intervals `[a n, b n]` and `[a m, b m]` overlap in a null set when `n ≠ m`. -/
theorem volume_inter_Icc_eq_zero {N : ℕ} {a b : ℕ → ℝ}
    (h_ordered : ∀ {n m}, 1 ≤ n → n ≤ N → 1 ≤ m → m ≤ N → n < m → b n ≤ a m)
    {n m : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) (hnm : n ≠ m) :
    volume (Set.Icc (a n) (b n) ∩ Set.Icc (a m) (b m)) = 0 := by
  have main : ∀ p q : ℕ, 1 ≤ p → p ≤ N → 1 ≤ q → q ≤ N → p < q →
      volume (Set.Icc (a p) (b p) ∩ Set.Icc (a q) (b q)) = 0 := by
    intro p q hp hpN hq hqN hpq
    have hle : b p ≤ a q := h_ordered hp hpN hq hqN hpq
    have hsub : Set.Icc (a p) (b p) ∩ Set.Icc (a q) (b q) ⊆ Set.Icc (a q) (b p) := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨hx2.1, hx1.2⟩
    have : volume (Set.Icc (a q) (b p)) = 0 := by
      rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
      linarith
    exact measure_mono_null hsub this
  rcases lt_or_gt_of_ne hnm with h | h
  · exact main n m hn hnN hm hmN h
  · rw [Set.inter_comm]
    exact main m n hm hmN hn hnN h

/-! ## The main theorem -/

/--
**Orthogonality relations.**

Given `a 1 < b 1 ≤ a 2 < b 2 ≤ ⋯ ≤ a N < b N` and functions `F n` on `[a n, b n]` with
`∫ s in [a n, b n], ‖F n s‖ ^ 2 = 1`, the functions
`f n x = ∫ s in [a n, b n], F n s * exp (2 π i s x)` satisfy
`∫ x, f n x * conj (f m x) = if n = m then 1 else 0`.
-/
theorem kammler_20
    (N : ℕ)
    (a b : ℕ → ℝ)
    (F : ℕ → ℝ → ℂ)
    (h_meas : ∀ n, AEStronglyMeasurable (F n) volume)
    (_h_nonempty :
      ∀ {n}, 1 ≤ n → n ≤ N → a n < b n)
    (h_ordered :
      ∀ {n m}, 1 ≤ n → n ≤ N → 1 ≤ m → m ≤ N → n < m → b n ≤ a m)
    (h_norm :
      ∀ {n}, 1 ≤ n → n ≤ N →
        ∫ s in Set.Icc (a n) (b n), ‖F n s‖ ^ (2 : ℕ) = 1) :
    ∀ {n m : ℕ}, 1 ≤ n → n ≤ N → 1 ≤ m → m ≤ N →
      ∫ x : ℝ,
        kammler_f a b F n x * star (kammler_f a b F m x)
      = (if n = m then (1 : ℂ) else 0) := by
  intro n m hn hnN hm hmN
  set g : ℕ → ℝ → ℂ := fun k => (Set.Icc (a k) (b k)).indicator (F k) with _hg
  have hI : ∀ {k}, 1 ≤ k → k ≤ N →
      IntegrableOn (fun s => ‖F k s‖ ^ (2 : ℕ)) (Set.Icc (a k) (b k)) volume :=
    fun hk hkN => integrableOn_sq_norm_of_integral_eq_one (h_norm hk hkN)
  have hmem : ∀ {k}, 1 ≤ k → k ≤ N → MemLp (g k) 2 volume :=
    fun hk hkN => memLp_two_indicator (h_meas _) (hI hk hkN)
  have hint : ∀ {k}, 1 ≤ k → k ≤ N → Integrable (g k) :=
    fun hk hkN => integrable_indicator_of_sq (h_meas _) (hI hk hkN)
  -- rewrite the integral in terms of the Fourier transform
  have hrw : ∫ x : ℝ, kammler_f a b F n x * star (kammler_f a b F m x)
      = ∫ x : ℝ, g n x * (starRingEnd ℂ) (g m x) := by
    have : ∀ x : ℝ, kammler_f a b F n x * star (kammler_f a b F m x)
        = (fun y : ℝ => 𝓕 (g n) y * (starRingEnd ℂ) (𝓕 (g m) y)) (-x) := by
      intro x
      rw [kammler_f_eq_fourier, kammler_f_eq_fourier]
      rfl
    calc ∫ x : ℝ, kammler_f a b F n x * star (kammler_f a b F m x)
        = ∫ x : ℝ, (fun y : ℝ => 𝓕 (g n) y * (starRingEnd ℂ) (𝓕 (g m) y)) (-x) :=
          integral_congr_ae (Filter.Eventually.of_forall this)
      _ = ∫ y : ℝ, 𝓕 (g n) y * (starRingEnd ℂ) (𝓕 (g m) y) :=
          integral_neg_eq_self (fun y : ℝ => 𝓕 (g n) y * (starRingEnd ℂ) (𝓕 (g m) y)) volume
      _ = ∫ x : ℝ, g n x * (starRingEnd ℂ) (g m x) :=
          integral_fourier_mul_conj_eq (g n) (g m) (hint hn hnN) (hmem hn hnN)
            (hint hm hmN) (hmem hm hmN)
  rw [hrw]
  by_cases hnm : n = m
  · subst hnm
    simp only [↓reduceIte]
    have hpt : ∀ x : ℝ, g n x * (starRingEnd ℂ) (g n x) = ((‖g n x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      intro x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
    have hEq : (fun x => ‖g n x‖ ^ (2 : ℕ))
        = (Set.Icc (a n) (b n)).indicator (fun s => ‖F n s‖ ^ (2 : ℕ)) := by
      funext x
      by_cases hx : x ∈ Set.Icc (a n) (b n) <;> simp [hx]
    rw [hEq, integral_indicator measurableSet_Icc, h_norm hn hnN]
    norm_num
  · simp only [hnm, ↓reduceIte]
    have hzero : ∀ᵐ x : ℝ, g n x * (starRingEnd ℂ) (g m x) = 0 := by
      have hnull := volume_inter_Icc_eq_zero (N := N) h_ordered hn hnN hm hmN hnm
      have := (MeasureTheory.measure_eq_zero_iff_ae_notMem (μ := volume)
        (s := Set.Icc (a n) (b n) ∩ Set.Icc (a m) (b m))).mp hnull
      filter_upwards [this] with x hx
      by_cases hxn : x ∈ Set.Icc (a n) (b n)
      · have hxm : x ∉ Set.Icc (a m) (b m) := fun h => hx ⟨hxn, h⟩
        simp [Set.indicator_of_notMem hxm]
      · simp [Set.indicator_of_notMem hxn]
    rw [integral_congr_ae hzero, integral_zero]
