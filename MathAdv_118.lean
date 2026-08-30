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

/-!
# Least-squares `σ`-bandlimited approximation (Kammler, Exercise 4.9)

Two students look for a `σ`-bandlimited approximation `g` of a function `f`: one minimizes the
continuous energy `∫ |f - g|²`, the other minimizes the sampled energy
`∑ₙ |f(nT) - g(nT)|²` with `T = 1/(2σ)`.

This file formalizes the two mathematical facts underlying the answer:

* `truncation_minimizes_L2` : on the spectrum side, truncation to the band `{|t| ≤ σ}` minimizes
  the `L²` error among all functions vanishing off the band;
* `kammler_25` : with the objectives `J_cont` and `J_disc` below, both minimization problems have
  solutions, exhibited explicitly.
-/

/-- `g` is (spectrum-side) `σ`-bandlimited: it vanishes outside the band `[-σ, σ]`. -/
def Bandlimited (σ : ℝ) (g : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, σ < |t| → g t = 0

/-- The continuous least-squares objective, integrated over the band `[-σ, σ]`. -/
noncomputable def J_cont (σ : ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∫ t in Set.Icc (-σ) σ, ‖f t - g t‖ ^ 2

/-- The sampled least-squares objective, over the sample points `k·T` with `T = 1/(2σ)` that lie
in the band. -/
noncomputable def J_disc (σ : ℝ) (f g : ℝ → ℂ) : ℝ :=
  let T : ℝ := 1 / (2 * σ)
  let N : ℤ := Int.floor (σ / T)
  ∑ n ∈ Finset.range (Int.toNat (2 * N + 1)),
    let k : ℤ := (n : ℤ) - N
    let t : ℝ := k * T
    ‖f t - g t‖ ^ 2

/-- The spectrum-side answer supplied by the Plancherel identity: among all functions `h`
vanishing off the band `{|t| ≤ σ}`, the truncation `1_{|t| ≤ σ} · F` of `F` minimizes the
`L²`-error `∫ ‖F - h‖²`. -/
theorem truncation_minimizes_L2 (σ : ℝ) (F h : ℝ → ℂ)
    (hh : ∀ t : ℝ, σ < |t| → h t = 0)
    (hint : MeasureTheory.Integrable (fun t : ℝ => ‖F t - h t‖ ^ 2)) :
    ∫ t : ℝ, ‖F t - Set.indicator {s : ℝ | |s| ≤ σ} F t‖ ^ 2
      ≤ ∫ t : ℝ, ‖F t - h t‖ ^ 2 := by
  have hmeas : MeasurableSet {s : ℝ | |s| ≤ σ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hpt : ∀ t : ℝ, ‖F t - Set.indicator {s : ℝ | |s| ≤ σ} F t‖ ^ 2
      = ({s : ℝ | |s| ≤ σ}ᶜ).indicator (fun t : ℝ => ‖F t - h t‖ ^ 2) t := by
    intro t
    by_cases ht : |t| ≤ σ
    · simp [Set.indicator_of_mem, ht]
    · have ht' : σ < |t| := lt_of_not_ge ht
      rw [Set.indicator_of_notMem (by simpa using ht'),
        Set.indicator_of_mem (by simpa using ht), hh t ht']
  calc ∫ t : ℝ, ‖F t - Set.indicator {s : ℝ | |s| ≤ σ} F t‖ ^ 2
      = ∫ t : ℝ, ({s : ℝ | |s| ≤ σ}ᶜ).indicator (fun t : ℝ => ‖F t - h t‖ ^ 2) t := by
        simp only [hpt]
    _ = ∫ t in {s : ℝ | |s| ≤ σ}ᶜ, ‖F t - h t‖ ^ 2 :=
        MeasureTheory.integral_indicator hmeas.compl
    _ ≤ ∫ t : ℝ, ‖F t - h t‖ ^ 2 :=
        MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall (fun _ => by positivity))

/-- The truncation `g₀ t = f t` for `|t| ≤ σ`, `g₀ t = 0` otherwise, is `σ`-bandlimited. -/
theorem bandlimited_trunc (σ : ℝ) (f : ℝ → ℂ) :
    Bandlimited σ (fun t : ℝ => if |t| ≤ σ then f t else 0) := by
  intro t ht
  simp [not_le.2 ht]

/-- Both objectives are nonnegative. -/
theorem J_cont_nonneg (σ : ℝ) (f g : ℝ → ℂ) : 0 ≤ J_cont σ f g :=
  MeasureTheory.integral_nonneg (fun _ => by positivity)

theorem J_disc_nonneg (σ : ℝ) (f g : ℝ → ℂ) : 0 ≤ J_disc σ f g :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- The truncation of `f` to the band makes the continuous objective vanish. -/
theorem J_cont_trunc_eq_zero (σ : ℝ) (f : ℝ → ℂ) :
    J_cont σ f (fun t : ℝ => if |t| ≤ σ then f t else 0) = 0 := by
  have : ∀ t ∈ Set.Icc (-σ) σ,
      ‖f t - (if |t| ≤ σ then f t else 0)‖ ^ 2 = 0 := by
    intro t ht
    have : |t| ≤ σ := abs_le.2 ⟨ht.1, ht.2⟩
    simp [this]
  unfold J_cont
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc this]
  simp

/-- The truncation of `f` to the band makes the sampled objective vanish: all the sample points
`k·T`, `|k| ≤ ⌊σ/T⌋`, lie inside the band. -/
theorem J_disc_trunc_eq_zero (σ : ℝ) (_hσ : 0 < σ) (f : ℝ → ℂ) :
    J_disc σ f (fun t : ℝ => if |t| ≤ σ then f t else 0) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro n hn
  simp only [Finset.mem_range] at hn
  set T : ℝ := 1 / (2 * σ) with _hT
  have hTpos : 0 < T := by positivity
  set N : ℤ := Int.floor (σ / T) with hN
  have hNle : (N : ℝ) ≤ σ / T := Int.floor_le _
  set k : ℤ := (n : ℤ) - N with _hk
  have _hN0 : 0 ≤ N := by
    rw [hN]
    exact Int.floor_nonneg.2 (by positivity)
  have _hn' : (n : ℤ) < 2 * N + 1 := by omega
  have hkabs : |(k : ℝ)| ≤ (N : ℝ) :=
    abs_le.2 ⟨by exact_mod_cast (show -N ≤ k by omega), by exact_mod_cast (show k ≤ N by omega)⟩
  have hkT : |(k : ℝ) * T| ≤ σ := by
    rw [abs_mul, abs_of_pos hTpos]
    calc |(k : ℝ)| * T ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hkabs hTpos.le
      _ ≤ (σ / T) * T := mul_le_mul_of_nonneg_right hNle hTpos.le
      _ = σ := by field_simp
  show ‖f ((k : ℝ) * T) - (if |(k : ℝ) * T| ≤ σ then f ((k : ℝ) * T) else 0)‖ ^ 2 = 0
  simp only [hkT, ↓reduceIte]
  simp

/-- **Kammler, Exercise 4.9.** For every `σ > 0` and every `f`, both least-squares problems
— the continuous one (`J_cont`) and the sampled one (`J_disc`, with `T = 1/(2σ)`) — admit
`σ`-bandlimited minimizers, obtained by keeping `f` on the band `[-σ, σ]` and setting it to `0`
outside. -/
theorem kammler_25
    (σ : ℝ) (hσ : 0 < σ)
    (f : ℝ → ℂ) :
    ∃ g₁ : ℝ → ℂ,
      Bandlimited σ g₁ ∧
      (∀ g, Bandlimited σ g → J_cont σ f g₁ ≤ J_cont σ f g)
    ∧
    ∃ g₂ : ℝ → ℂ,
      Bandlimited σ g₂ ∧
      (∀ g, Bandlimited σ g → J_disc σ f g₂ ≤ J_disc σ f g) := by
  refine ⟨fun t : ℝ => if |t| ≤ σ then f t else 0, bandlimited_trunc σ f, ?_,
    ⟨fun t : ℝ => if |t| ≤ σ then f t else 0, bandlimited_trunc σ f, ?_⟩⟩
  · intro g _
    rw [J_cont_trunc_eq_zero σ f]
    exact J_cont_nonneg σ f g
  · intro g _
    rw [J_disc_trunc_eq_zero σ hσ f]
    exact J_disc_nonneg σ f g
