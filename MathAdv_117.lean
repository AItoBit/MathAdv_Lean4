import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped FourierTransform

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# The Fourier transform of the Haar wavelet

We define the Haar wavelet

```
ψ x = 1   for 0 ≤ x < 1/2
ψ x = -1  for 1/2 ≤ x < 1
ψ x = 0   otherwise
```

and compute its Fourier transform (with the convention
`𝓕 f s = ∫ x, exp (-2 π i x s) * f x`, which is the one used in Mathlib and in Kammler's
book), obtaining

```
Ψ s = i e^{-i π s} sin (π s / 2) sinc (s / 2),
```

where `sinc` is the *normalized* cardinal sine `sinc x = sin (π x) / (π x)` (with `sinc 0 = 1`),
i.e. `sincN` below.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral

/-- The Haar wavelet: `1` on `[0, 1/2)`, `-1` on `[1/2, 1)`, and `0` elsewhere. -/
def haarPsi (x : ℝ) : ℂ :=
  if 0 ≤ x ∧ x < 1 / 2 then 1 else if 1 / 2 ≤ x ∧ x < 1 then -1 else 0

/-- The normalized cardinal sine function, `sincN x = sin (π x) / (π x)`, with `sincN 0 = 1`. -/
def sincN (x : ℝ) : ℝ := Real.sinc (Real.pi * x)

lemma sincN_apply {x : ℝ} (hx : x ≠ 0) : sincN x = Real.sin (Real.pi * x) / (Real.pi * x) := by
  have h : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  simp [sincN, Real.sinc, h]

/-- The Haar wavelet is integrable, so its Fourier integral is genuinely convergent. -/
lemma haarPsi_integrable : Integrable haarPsi := by
  have hind : ∀ a b : ℝ, Integrable ((Set.Ico a b).indicator (fun _ : ℝ => (1 : ℂ))) := fun a b =>
    (((continuous_const (y := (1 : ℂ))).integrableOn_Icc (a := a) (b := b)).mono_set
      Set.Ico_subset_Icc_self).integrable_indicator measurableSet_Ico
  have h : haarPsi = fun x : ℝ =>
      (Set.Ico (0:ℝ) (1/2)).indicator (fun _ : ℝ => (1 : ℂ)) x
        - (Set.Ico (1/2:ℝ) 1).indicator (fun _ : ℝ => (1 : ℂ)) x := by
    funext x
    simp only [haarPsi, Set.indicator_apply, Set.mem_Ico]
    split_ifs with h1 h2 h3 <;> simp_all
    all_goals linarith
  rw [h]
  exact (hind _ _).sub (hind _ _)

/-- The Fourier integral of the Haar wavelet, written as a difference of two interval
integrals. -/
lemma fourier_haarPsi_eq (s : ℝ) :
    𝓕 haarPsi s =
      (∫ x in (0:ℝ)..(1/2), Complex.exp ((-2 * Real.pi * Complex.I * s) * x)) -
        (∫ x in (1/2:ℝ)..1, Complex.exp ((-2 * Real.pi * Complex.I * s) * x)) := by
  set c : ℂ := -2 * Real.pi * Complex.I * s with hc
  have hcont : Continuous (fun v : ℝ => Complex.exp (c * v)) := by fun_prop
  have hsub : ∀ a b : ℝ, a ≤ b →
      ∫ v, (Set.Ico a b).indicator (fun v : ℝ => Complex.exp (c * v)) v
        = ∫ v in a..b, Complex.exp (c * v) := by
    intro a b hab
    rw [MeasureTheory.integral_indicator measurableSet_Ico,
      MeasureTheory.integral_Ico_eq_integral_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hab]
  have hint : ∀ a b : ℝ,
      Integrable ((Set.Ico a b).indicator (fun v : ℝ => Complex.exp (c * v))) := fun a b =>
    ((hcont.integrableOn_Icc (a := a) (b := b)).mono_set
      Set.Ico_subset_Icc_self).integrable_indicator measurableSet_Ico
  rw [Real.fourier_eq']
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  have key : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * (s * v)) * Complex.I) * haarPsi v
      = (Set.Ico (0:ℝ) (1/2)).indicator (fun v : ℝ => Complex.exp (c * v)) v
        - (Set.Ico (1/2:ℝ) 1).indicator (fun v : ℝ => Complex.exp (c * v)) v := by
    intro v
    have hexp : Complex.exp (↑(-2 * Real.pi * (s * v)) * Complex.I) = Complex.exp (c * v) := by
      rw [hc]; congr 1; push_cast; ring
    rw [hexp]
    simp only [haarPsi, Set.indicator_apply, Set.mem_Ico]
    split_ifs with h1 h2 h3 <;> simp_all
    all_goals linarith
  simp_rw [key]
  rw [MeasureTheory.integral_sub (hint _ _) (hint _ _), hsub 0 (1/2) (by norm_num),
    hsub (1/2) 1 (by norm_num)]

/-- Value of the difference of the two interval integrals, for a nonzero exponent. -/
lemma haar_exp_integral {c : ℂ} (hc : c ≠ 0) :
    ((∫ x in (0:ℝ)..(1/2), Complex.exp (c * x)) - ∫ x in (1/2:ℝ)..1, Complex.exp (c * x)) =
      -(Complex.exp (c / 2) - 1) ^ 2 / c := by
  have hE : Complex.exp c = Complex.exp (c / 2) ^ 2 := by
    rw [sq, ← Complex.exp_add]; ring_nf
  rw [integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  push_cast
  rw [show c * (1 / 2 : ℂ) = c / 2 by ring, mul_one, mul_zero, Complex.exp_zero, hE]
  field_simp
  ring

/-- The algebraic identity behind the final form of the answer, for `s ≠ 0`. -/
lemma haar_exp_eq_sinc {s : ℝ} (hs : s ≠ 0) :
    -(Complex.exp ((-2 * Real.pi * Complex.I * s) / 2) - 1) ^ 2 / (-2 * Real.pi * Complex.I * s) =
      Complex.I * Complex.exp (-Complex.I * Real.pi * s) *
        (Real.sin (Real.pi * s / 2) : ℂ) * (sincN (s / 2) : ℂ) := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hs2 : s / 2 ≠ 0 := by simpa using hs
  have hsinc : sincN (s / 2) = Real.sin (Real.pi * s / 2) / (Real.pi * s / 2) := by
    rw [sincN_apply hs2]; ring_nf
  rw [hsinc]
  set t : ℝ := Real.pi * s / 2 with ht
  have htne0 : t ≠ 0 := div_ne_zero (mul_ne_zero hpi hs) two_ne_zero
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htne0
  set X : ℂ := Complex.exp (Complex.I * t) with hX
  have hXne : X ≠ 0 := Complex.exp_ne_zero _
  have hsin : Complex.sin (t : ℂ) = (X⁻¹ - X) * Complex.I / 2 := by
    rw [Complex.sin, hX, ← Complex.exp_neg]
    ring_nf
  have hexp2 : Complex.exp (-Complex.I * Real.pi * s) = X⁻¹ * X⁻¹ := by
    rw [hX, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast [ht]
    ring
  have hc2 : (-2 * (Real.pi : ℂ) * Complex.I * s) / 2 = -Complex.I * Real.pi * s := by ring
  have hden : (-2 * (Real.pi : ℂ) * Complex.I * s) = -4 * Complex.I * t := by
    push_cast [ht]; ring
  have h4 : Complex.I ^ 4 = 1 := by simp [pow_succ]
  rw [hc2, hexp2, hden]
  push_cast
  rw [hsin]
  field_simp
  ring_nf
  rw [h4]
  ring

/-- **The Fourier transform of the Haar wavelet.**

With the convention `𝓕 f s = ∫ x, exp (-2 π i x s) * f x`, the Haar wavelet `haarPsi` has
Fourier transform `Ψ s = i e^{-i π s} sin (π s / 2) sinc (s / 2)`, where `sinc` is the
normalized cardinal sine `sincN`. -/
theorem fourier_haarPsi (s : ℝ) :
    𝓕 haarPsi s =
      Complex.I * Complex.exp (-Complex.I * Real.pi * s) *
        (Real.sin (Real.pi * s / 2) : ℂ) * (sincN (s / 2) : ℂ) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [fourier_haarPsi_eq]
    norm_num
  · have hcne : (-2 * (Real.pi : ℂ) * Complex.I * s) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hs)
    rw [fourier_haarPsi_eq, haar_exp_integral hcne, haar_exp_eq_sinc hs]

/-- Any real-valued function satisfying the defining conditions of the Haar wavelet agrees
with `haarPsi`. -/
lemma coe_eq_haarPsi {psi : ℝ → ℝ}
    (h0 : ∀ x, 0 ≤ x ∧ x < (1 / 2 : ℝ) → psi x = 1)
    (h1 : ∀ x, (1 / 2 : ℝ) ≤ x ∧ x < 1 → psi x = -1)
    (hout : ∀ x, (x < 0 ∨ 1 ≤ x) → psi x = 0) :
    (fun x : ℝ => (psi x : ℂ)) = haarPsi := by
  funext x
  simp only [haarPsi]
  split_ifs with hA hB
  · rw [h0 x hA]; norm_num
  · rw [h1 x hB]; norm_num
  · have hx : x < 0 ∨ 1 ≤ x := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hx1⟩ := hcon
      rcases lt_or_ge x (1 / 2 : ℝ) with h | h
      · exact hA ⟨hx0, h⟩
      · exact hB ⟨h, hx1⟩
    rw [hout x hx]; norm_num

/-- **Fourier transform of the Haar wavelet**, stated for an arbitrary real-valued function
`psi` specified by the three defining conditions. -/
theorem fourier_haar_wavelet (psi : ℝ → ℝ)
    (h0 : ∀ x, 0 ≤ x ∧ x < (1 / 2 : ℝ) → psi x = 1)
    (h1 : ∀ x, (1 / 2 : ℝ) ≤ x ∧ x < 1 → psi x = -1)
    (hout : ∀ x, (x < 0 ∨ 1 ≤ x) → psi x = 0) :
    𝓕 (fun x : ℝ => (psi x : ℂ)) = fun s : ℝ =>
      Complex.I * Complex.exp (-Complex.I * Real.pi * s) *
        (Real.sin (Real.pi * s / 2) : ℂ) * (sincN (s / 2) : ℂ) := by
  rw [coe_eq_haarPsi h0 h1 hout]
  funext s
  exact fourier_haarPsi s

/-
The statement below is the originally proposed formalization. It cannot be proved: both the
Fourier transform `Fourier` and the cardinal sine `sinc` occur there as *arbitrary* function
variables, with no hypothesis relating them to the actual Fourier transform and to
`sin (π x) / (π x)`. Taking, e.g., `Fourier := fun _ _ => 0` and `sinc := fun _ => 1` makes the
conclusion false. The faithful versions are `fourier_haarPsi` and `fourier_haar_wavelet` above,
which use Mathlib's Fourier transform `𝓕` and the normalized cardinal sine `sincN`.

noncomputable def haarPsi' (s : ℝ) (sinc : ℝ → ℝ) : ℂ :=
  Complex.I *
    Complex.exp (-Complex.I * Real.pi * s) *
    (Real.sin (Real.pi * s / 2) : ℂ) *
    ((sinc (s / 2)) : ℂ)

theorem kammler_26_a
    (ψ : ℝ → ℝ)
    (h0 : ∀ x, 0 ≤ x ∧ x < (1 / 2 : ℝ) → ψ x = 1)
    (h1 : ∀ x, (1 / 2 : ℝ) ≤ x ∧ x < 1 → ψ x = -1)
    (hout : ∀ x, (x < 0 ∨ 1 ≤ x) → ψ x = 0)
    (Fourier : (ℝ → ℝ) → ℝ → ℂ)
    (sinc : ℝ → ℝ) :
    Fourier ψ = fun s : ℝ => haarPsi' s sinc := by
  sorry
-/

end
