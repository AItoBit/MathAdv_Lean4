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

/-! # Continuous nowhere-differentiable functions are dense in `C([0,1], ℝ)`

Let `K = [0,1]`, `X = C(K, ℝ)` and for `n ≥ 1`
`F n = {f ∈ X : ∃ t ∈ K, ∀ h with t + h ∈ K, |(f (t+h) - f t)/h| ≤ n}`.

We show that each `F n` is closed and nowhere dense, and deduce (via the Baire
category theorem) that the set of continuous nowhere-differentiable functions on
`K` is dense in `X`. -/

namespace Bollobas516

/-- The unit interval as a compact topological space. -/
abbrev I : Set ℝ := Set.Icc (0 : ℝ) 1

/-- The extension by `0` of `f ∈ C([0,1], ℝ)` to all of `ℝ`. -/
noncomputable def ext (f : C(I, ℝ)) : ℝ → ℝ :=
  fun x => if hx : x ∈ I then f ⟨x, hx⟩ else 0

/-- The sets `F n` of the problem. -/
def F (n : ℕ) : Set C(I, ℝ) :=
  { f | ∃ (t : ℝ) (ht : t ∈ I), ∀ (h : ℝ) (hth : t + h ∈ I),
      ‖(f ⟨t + h, hth⟩ - f ⟨t, ht⟩) / h‖ ≤ n }

/-- If `f`, extended by zero, is differentiable at some `t ∈ [0,1]`, then all its
difference quotients at `t` are bounded by a single constant. -/
theorem exists_bound_of_differentiableAt (f : C(I, ℝ)) (t : ℝ) (ht : t ∈ I)
    (hd : DifferentiableAt ℝ (ext f) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (hth : t + h ∈ I),
      ‖(f ⟨t + h, hth⟩ - f ⟨t, ht⟩) / h‖ ≤ C := by
  obtain ⟨c, hc⟩ := hd.hasFDerivAt.isBigO_sub.bound
  rw [Metric.eventually_nhds_iff] at hc
  obtain ⟨δ, hδ, hbd⟩ := hc
  refine ⟨max (max c 0) (2 * ‖f‖ / δ), le_max_of_le_left (le_max_right _ _), ?_⟩
  intro h hth
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hft : ext f t = f ⟨t, ht⟩ := by simp [ext, ht]
  have hfth : ext f (t + h) = f ⟨t + h, hth⟩ := by simp [ext, hth]
  rcases lt_or_ge |h| δ with hlt | hge
  · have := hbd (y := t + h) (by simpa [Real.dist_eq, abs_sub_comm] using hlt)
    rw [hft, hfth] at this
    have hnorm : ‖f ⟨t + h, hth⟩ - f ⟨t, ht⟩‖ ≤ c * |h| := by
      simpa [Real.norm_eq_abs] using this
    have hhpos : (0:ℝ) < |h| := abs_pos.mpr hh
    have : ‖(f ⟨t + h, hth⟩ - f ⟨t, ht⟩) / h‖ ≤ c := by
      simp only [norm_div, Real.norm_eq_abs] at hnorm ⊢
      rw [div_le_iff₀ hhpos]
      exact hnorm
    exact this.trans (le_max_of_le_left (le_max_left _ _))
  · have h1 : ‖f ⟨t + h, hth⟩ - f ⟨t, ht⟩‖ ≤ 2 * ‖f‖ := by
      calc ‖f ⟨t + h, hth⟩ - f ⟨t, ht⟩‖ ≤ ‖f ⟨t + h, hth⟩‖ + ‖f ⟨t, ht⟩‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    have hhpos : (0:ℝ) < |h| := lt_of_lt_of_le hδ hge
    have : ‖(f ⟨t + h, hth⟩ - f ⟨t, ht⟩) / h‖ ≤ 2 * ‖f‖ / δ := by
      simp only [norm_div, Real.norm_eq_abs] at h1 ⊢
      rw [div_le_div_iff₀ hhpos hδ]
      have hf0 : (0:ℝ) ≤ 2 * ‖f‖ := by positivity
      calc ‖f ⟨t + h, hth⟩ - f ⟨t, ht⟩‖ * δ ≤ (2 * ‖f‖) * δ :=
            mul_le_mul_of_nonneg_right h1 hδ.le
        _ ≤ (2 * ‖f‖) * |h| := mul_le_mul_of_nonneg_left hge hf0
    exact this.trans (le_max_right _ _)

/-- A function which is differentiable (after extension by zero) at some point of `[0,1]`
belongs to some `F n` with `n ≥ 1`. -/
theorem mem_F_of_differentiableAt (f : C(I, ℝ)) (t : ℝ) (ht : t ∈ I)
    (hd : DifferentiableAt ℝ (ext f) t) : ∃ n : ℕ, 1 ≤ n ∧ f ∈ F n := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_differentiableAt f t ht hd
  refine ⟨⌈C⌉₊ + 1, by omega, t, ht, fun h hth => ?_⟩
  refine (hC h hth).trans ?_
  have : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  push_cast
  linarith

/-- Reformulation of membership in `F n`: `f ∈ F n` iff `f` satisfies a Lipschitz-type
estimate at some point `t ∈ [0,1]`. -/
theorem mem_F_iff (n : ℕ) (f : C(I, ℝ)) :
    f ∈ F n ↔ ∃ t : I, ∀ s : I, |f s - f t| ≤ n * |(s : ℝ) - (t : ℝ)| := by
  constructor
  · rintro ⟨t, ht, hb⟩
    refine ⟨⟨t, ht⟩, fun s => ?_⟩
    have hth : t + ((s : ℝ) - t) ∈ I := by
      have h : t + ((s : ℝ) - t) = (s : ℝ) := by ring
      rw [h]; exact s.2
    have hb' := hb ((s : ℝ) - t) hth
    have hse : (⟨t + ((s : ℝ) - t), hth⟩ : I) = s := Subtype.ext (by simp)
    rw [hse] at hb'
    rcases eq_or_ne ((s : ℝ) - t) 0 with h0 | h0
    · have hst : s = (⟨t, ht⟩ : I) := Subtype.ext (by linarith [sub_eq_zero.mp h0])
      simp [hst]
    · have hpos : (0:ℝ) < |(s:ℝ) - t| := abs_pos.mpr h0
      simp only [norm_div, Real.norm_eq_abs] at hb'
      rw [div_le_iff₀ hpos] at hb'
      exact hb'
  · rintro ⟨t, hb⟩
    refine ⟨(t : ℝ), t.2, fun h hth => ?_⟩
    rcases eq_or_ne h 0 with rfl | h0
    · simp
    · have hpos : (0:ℝ) < |h| := abs_pos.mpr h0
      have hbt := hb ⟨(t : ℝ) + h, hth⟩
      simp only [norm_div, Real.norm_eq_abs]
      rw [div_le_iff₀ hpos]
      have ht' : ((⟨(t:ℝ), t.2⟩ : I)) = t := Subtype.ext rfl
      simp only [ht'] at *
      calc |f ⟨(t:ℝ) + h, hth⟩ - f t| ≤ (n:ℝ) * |((t:ℝ) + h) - (t:ℝ)| := hbt
        _ = (n:ℝ) * |h| := by ring_nf

/-- Each `F n` is closed: it is the image under the (closed) projection
`I × C(I,ℝ) → C(I,ℝ)` of a closed set. -/
theorem isClosed_F (n : ℕ) : IsClosed (F n) := by
  set S : Set (I × C(I, ℝ)) :=
    {p | ∀ s : I, |p.2 s - p.2 p.1| ≤ (n : ℝ) * |(s : ℝ) - (p.1 : ℝ)|} with hSdef
  have hS : IsClosed S := by
    have hEq : S =
        ⋂ s : I, {p : I × C(I, ℝ) | |p.2 s - p.2 p.1| ≤ (n : ℝ) * |(s : ℝ) - (p.1 : ℝ)|} := by
      ext p; simp [hSdef]
    rw [hEq]
    refine isClosed_iInter fun s => isClosed_le ?_ ?_
    · exact ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).sub
        (continuous_eval.comp (continuous_snd.prodMk continuous_fst))).abs
    · exact continuous_const.mul
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).abs)
  have himg : F n = Prod.snd '' S := by
    ext f
    constructor
    · intro hf
      obtain ⟨t, ht⟩ := (mem_F_iff n f).mp hf
      exact ⟨(t, f), ht, rfl⟩
    · rintro ⟨⟨t, g⟩, hg, rfl⟩
      exact (mem_F_iff n _).mpr ⟨t, hg⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace S hS

/-- A chord estimate for the sine function: from any point `u`, moving by `π/2` or by
`3π/2` in a prescribed direction changes the value of `sin` by at least `1`. -/
theorem exists_sin_chord (u σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ d : ℝ, (d = σ * (Real.pi/2) ∨ d = σ * (3*Real.pi/2)) ∧
      1 ≤ |Real.sin (u + d) - Real.sin u| := by
  have h1 : Real.sin (u + σ * (Real.pi/2)) = σ * Real.cos u := by
    rcases hσ with rfl | rfl <;>
      simp [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  have h3 : Real.sin (3*Real.pi/2) = -1 := by
    have h : (3*Real.pi/2) = Real.pi + Real.pi/2 := by ring
    rw [h, Real.sin_add]; simp
  have h4 : Real.cos (3*Real.pi/2) = 0 := by
    have h : (3*Real.pi/2) = Real.pi + Real.pi/2 := by ring
    rw [h, Real.cos_add]; simp
  have h2 : Real.sin (u + σ * (3*Real.pi/2)) = -(σ * Real.cos u) := by
    rcases hσ with rfl | rfl <;> simp [Real.sin_add, h3, h4]
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set A := σ * Real.cos u - Real.sin u with hA
  set B := -(σ * Real.cos u) - Real.sin u with hB
  have hsum : A^2 + B^2 = 2 := by
    have hpyth := Real.sin_sq_add_cos_sq u
    simp only [hA, hB]
    nlinarith [hpyth, hσ2]
  by_cases hcase : 1 ≤ |A|
  · exact ⟨σ * (Real.pi/2), Or.inl rfl, by rw [h1]; exact hcase⟩
  · refine ⟨σ * (3*Real.pi/2), Or.inr rfl, ?_⟩
    rw [h2]
    push_neg at hcase
    have hA2 : A^2 < 1 := by nlinarith [abs_nonneg A, sq_abs A]
    have hB2 : 1 < B^2 := by nlinarith
    nlinarith [abs_nonneg B, sq_abs B]

/-- An elementary arithmetic bound used in the proof that `F n` has empty interior. -/
theorem aux_cast_bound (n : ℕ) {a r x : ℝ} (hapos : 0 < a) (hx : x ≤ r/2)
    (hra : r ≤ a / (2*((n:ℝ)+1))) : (n:ℝ) * x < a/2 := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h1 : (n:ℝ) * x ≤ (n:ℝ) * (r/2) := mul_le_mul_of_nonneg_left hx hn0
  have h2 : (n:ℝ) * (r/2) ≤ (n:ℝ) * (a / (2*((n:ℝ)+1)) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hn0
  have hfrac : (n:ℝ) / ((n:ℝ)+1) ≤ 1 := by rw [div_le_one hn1]; linarith
  have heq : (n:ℝ) * (a / (2*((n:ℝ)+1)) / 2) = (a/4) * ((n:ℝ)/((n:ℝ)+1)) := by
    field_simp; ring
  have h4 : (a/4) * ((n:ℝ)/((n:ℝ)+1)) ≤ (a/4) * 1 :=
    mul_le_mul_of_nonneg_left hfrac (by positivity)
  rw [heq] at h2
  linarith

/-- Every function in `X` can be approximated, to within any `ε > 0`, by a function which
is not in `F n`: it suffices to add a small sine wave of very high frequency. -/
theorem exists_notMem_F_close (n : ℕ) (f : C(I, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(I, ℝ), dist f g < ε ∧ g ∉ F n := by
  set a : ℝ := ε / 2 with ha
  have hapos : 0 < a := by positivity
  obtain ⟨δ, hδ, hδf⟩ : ∃ δ > 0, ∀ x y : I, dist x y < δ → dist (f x) (f y) < a / 2 := by
    have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp hu (a/2) (by positivity)
    exact ⟨δ, hδ, fun x y hxy => h hxy⟩
  set r : ℝ := min (min δ (1/2)) (a / (2*(n+1))) with hr
  have hrpos : 0 < r := by
    have h1 : 0 < a / (2*(n+1)) := by positivity
    simp only [hr, lt_min_iff]
    exact ⟨⟨hδ, by norm_num⟩, h1⟩
  have hrle1 : r ≤ 1/2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrδ : r ≤ δ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hra : r ≤ a / (2*(n+1)) := min_le_right _ _
  have hpi := Real.pi_pos
  set m : ℝ := 3*Real.pi/r with hm
  have hmpos : 0 < m := by positivity
  set sw : C(I, ℝ) := ⟨fun x : I => Real.sin (m * x), by fun_prop⟩ with hsw
  set g : C(I, ℝ) := f + a • sw with hg
  have hgapp : ∀ x : I, g x = f x + a * Real.sin (m * x) := by intro x; simp [hg, hsw]
  refine ⟨g, ?_, ?_⟩
  · have hle : dist f g ≤ a := by
      rw [ContinuousMap.dist_le hapos.le]
      intro x
      rw [Real.dist_eq, hgapp x]
      have h1 := Real.abs_sin_le_one (m * x)
      have h2 : |f x - (f x + a * Real.sin (m * x))| = a * |Real.sin (m * x)| := by
        rw [show f x - (f x + a * Real.sin (m * x)) = -(a * Real.sin (m*x)) by ring,
          abs_neg, abs_mul, abs_of_pos hapos]
      rw [h2]
      nlinarith [abs_nonneg (Real.sin (m * x))]
    have hlt : a < ε := by rw [ha]; linarith
    linarith
  · intro hmem
    obtain ⟨t, ht⟩ := (mem_F_iff n g).mp hmem
    set σ : ℝ := if (t:ℝ) ≤ 1/2 then 1 else -1 with hσdef
    have hσ1 : σ = 1 ∨ σ = -1 := by simp only [hσdef]; split <;> simp
    obtain ⟨d, hd, hchord⟩ := exists_sin_chord (m * t) σ hσ1
    obtain ⟨c, hc1, hc2, hdc⟩ : ∃ c : ℝ, Real.pi/2 ≤ c ∧ c ≤ 3*Real.pi/2 ∧ d = σ * c := by
      rcases hd with rfl | rfl
      · exact ⟨Real.pi/2, le_refl _, by linarith, rfl⟩
      · exact ⟨3*Real.pi/2, by linarith, le_refl _, rfl⟩
    have hcpos : 0 < c := by linarith
    have hσabs : |σ| = 1 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
    have hdabs : |d| = c := by simp [hdc, abs_mul, hσabs, abs_of_pos hcpos]
    have hmr : (3*Real.pi/2)/m = r/2 := by rw [hm]; field_simp
    have hdm : |d/m| ≤ r/2 := by
      rw [abs_div, abs_of_pos hmpos, hdabs, ← hmr]
      gcongr
    have hdmpos : 0 < |d/m| := by
      rw [abs_div, abs_of_pos hmpos, hdabs]; positivity
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    have hb : |d/m| ≤ 1/4 := by linarith
    have hb2 : -(1/4:ℝ) ≤ d/m ∧ d/m ≤ 1/4 := abs_le.mp hb
    have hs : (t:ℝ) + d/m ∈ I := by
      constructor
      · by_cases hcase : (t:ℝ) ≤ 1/2
        · have hσ' : σ = 1 := by rw [hσdef, if_pos hcase]
          have hd0 : 0 ≤ d/m := by rw [hdc, hσ', one_mul]; positivity
          linarith
        · push_neg at hcase
          linarith [hb2.1]
      · by_cases hcase : (t:ℝ) ≤ 1/2
        · linarith [hb2.2]
        · push_neg at hcase
          have hσ' : σ = -1 := by rw [hσdef, if_neg (by push_neg; exact hcase)]
          have hd0 : d/m ≤ 0 := by
            rw [hdc, hσ', neg_one_mul, neg_div]
            have hcm : 0 ≤ c/m := by positivity
            linarith
          linarith
    set s : I := ⟨(t:ℝ) + d/m, hs⟩ with hsdef
    have hst : (s : ℝ) - (t:ℝ) = d/m := by simp [hsdef]
    have hmsin : m * (s:ℝ) = m * (t:ℝ) + d := by rw [hsdef]; field_simp
    have hfclose : |f s - f t| < a/2 := by
      have hdist : dist s t < δ := by
        rw [Subtype.dist_eq, Real.dist_eq, hst]
        linarith
      have hd' := hδf s t hdist
      rwa [Real.dist_eq] at hd'
    have hlower : a/2 ≤ |g s - g t| := by
      have hexp : g s - g t
          = a * (Real.sin (m * (t:ℝ) + d) - Real.sin (m * (t:ℝ))) + (f s - f t) := by
        rw [hgapp s, hgapp t, hmsin]; ring
      have h1 : a * 1 ≤ a * |Real.sin (m * (t:ℝ) + d) - Real.sin (m * (t:ℝ))| :=
        mul_le_mul_of_nonneg_left hchord hapos.le
      have h2 : |a * (Real.sin (m * (t:ℝ) + d) - Real.sin (m * (t:ℝ)))|
          = a * |Real.sin (m * (t:ℝ) + d) - Real.sin (m * (t:ℝ))| := by
        rw [abs_mul, abs_of_pos hapos]
      have h3 := abs_sub_abs_le_abs_sub
        (a * (Real.sin (m * (t:ℝ) + d) - Real.sin (m * (t:ℝ)))) (-(f s - f t))
      rw [sub_neg_eq_add, abs_neg] at h3
      rw [hexp]
      linarith
    have hupper : |g s - g t| ≤ (n:ℝ) * |d/m| := by
      have hts := ht s
      rwa [hst] at hts
    have hn := aux_cast_bound n hapos hdm hra
    linarith

/-- Each `F n` is nowhere dense. -/
theorem isNowhereDense_F (n : ℕ) : IsNowhereDense (F n) := by
  rw [(isClosed_F n).isNowhereDense_iff]
  refine interior_eq_empty_iff_dense_compl.mpr (Metric.dense_iff.mpr fun f ρ hρ => ?_)
  obtain ⟨g, hdist, hg⟩ := exists_notMem_F_close n f hρ
  exact ⟨g, Metric.mem_ball.mpr (by rwa [dist_comm]), hg⟩

end Bollobas516

theorem bollobas_5_16
  (K : Set ℝ) (hK : K = Set.Icc 0 1)
    (F : ℕ → Set (ContinuousMap (Set.Icc 0 1) ℝ))
    (hF : ∀ n : ℕ,
    F n = { f | ∃ (t : ℝ) (ht : t ∈ Set.Icc 0 1),
      ∀ (h : ℝ) (hth : t + h ∈ Set.Icc 0 1),
        ‖(f ⟨t + h, hth⟩ - f ⟨t, ht⟩) / h‖ ≤ n })
  (hFn_closed : ∀ n : ℕ, 1 ≤ n → IsClosed (F n))
  (hFn_nowhere : ∀ n : ℕ, 1 ≤ n → IsNowhereDense (F n)) :
  Dense { f : ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ |
    ∀ t (ht : t ∈ Set.Icc 0 1),
      ¬DifferentiableAt ℝ (fun x ↦ if hx : x ∈ Set.Icc 0 1 then f ⟨x, hx⟩ else 0) t } := by
  have hsub : (⋂ n : ℕ, (F (n + 1))ᶜ) ⊆
      { f : ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ |
        ∀ t (ht : t ∈ Set.Icc 0 1),
          ¬DifferentiableAt ℝ (fun x ↦ if hx : x ∈ Set.Icc 0 1 then f ⟨x, hx⟩ else 0) t } := by
    intro f hf t ht hd
    obtain ⟨n, hn1, hn⟩ := Bollobas516.mem_F_of_differentiableAt f t ht hd
    have : f ∈ F n := by rw [hF n]; exact hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    exact (Set.mem_iInter.mp hf m) this
  refine Dense.mono hsub (dense_iInter_of_isOpen (fun n => (hFn_closed (n+1) (by omega)).isOpen_compl)
    (fun n => ?_))
  have hnd := hFn_nowhere (n + 1) (by omega)
  rw [(hFn_closed (n+1) (by omega)).isNowhereDense_iff] at hnd
  exact interior_eq_empty_iff_dense_compl.mp hnd

/-- **Conclusion of the exercise, unconditionally**: the set of continuous real-valued
functions on `K = [0,1]` that are nowhere differentiable is dense in `X = C(K, ℝ)`.
Differentiability at `t ∈ K` is understood as differentiability at `t` of the extension of
`f` by `0` to all of `ℝ`.  The closedness and nowhere-density of the sets `F n`, which are
hypotheses in `bollobas_5_16`, are supplied here by `Bollobas516.isClosed_F` and
`Bollobas516.isNowhereDense_F`. -/
theorem dense_nowhereDifferentiable :
    Dense { f : ContinuousMap (Set.Icc (0:ℝ) 1) ℝ |
      ∀ t (ht : t ∈ Set.Icc (0:ℝ) 1),
        ¬DifferentiableAt ℝ (fun x => if hx : x ∈ Set.Icc (0:ℝ) 1 then f ⟨x, hx⟩ else 0) t } :=
  bollobas_5_16 (Set.Icc 0 1) rfl Bollobas516.F (fun _ => rfl)
    (fun n _ => Bollobas516.isClosed_F n) (fun n _ => Bollobas516.isNowhereDense_F n)
