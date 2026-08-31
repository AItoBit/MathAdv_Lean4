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

set_option autoImplicit false

set_option grind.warning false

/-! # Lee, Problem 5-10

For each `a ∈ ℝ` let `M a = {(x,y) : y² = x(x-1)(x-a)}`. Then `M a` is an embedded
submanifold of `ℝ²` (in the sense of being a regular level set of a `C¹` function,
i.e. the regular value theorem applies) if and only if `a ∉ {0, 1}`.
-/

abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- A subset of `ℝ²` is an embedded (codimension-one) submanifold when it is a regular
level set: the zero set of a `C¹` function whose differential is nonzero along that set. -/
def IsEmbeddedSubmanifold (S : Set R2) : Prop :=
  ∃ f : R2 → ℝ,
    ContDiff ℝ 1 f ∧
    S = {p : R2 | f p = 0} ∧
    (∀ p : R2, f p = 0 → fderiv ℝ f p ≠ 0)

namespace Lee510

/-- The `i`-th coordinate functional on `ℝ²`. -/
noncomputable def P (i : Fin 2) : R2 →L[ℝ] ℝ := EuclideanSpace.proj i

@[simp] lemma P_apply (i : Fin 2) (q : R2) : P i q = q i := rfl

/-- The `i`-th standard basis vector of `ℝ²`. -/
noncomputable def E (i : Fin 2) : R2 := EuclideanSpace.single i (1 : ℝ)

@[simp] lemma E_apply (i j : Fin 2) : (E i) j = if j = i then 1 else 0 := by
  simp [E]

lemma coord_decomp (w : R2) : w = (w 0) • E 0 + (w 1) • E 1 := by
  ext i; fin_cases i <;> simp

/-- A linear functional on `ℝ²` vanishing on both basis vectors is zero. -/
lemma clm_eq_zero (L : R2 →L[ℝ] ℝ) (h0 : L (E 0) = 0) (h1 : L (E 1) = 0) : L = 0 := by
  ext w
  rw [coord_decomp w]
  simp [h0, h1]

lemma abs_coord_le_norm (q : R2) (i : Fin 2) : |q i| ≤ ‖q‖ := by
  rw [EuclideanSpace.norm_eq]
  rw [show |q i| = Real.sqrt (|q i| ^ 2) by rw [Real.sqrt_sq (abs_nonneg _)]]
  apply Real.sqrt_le_sqrt
  have : |q i| ^ 2 ≤ ∑ j, ‖q j‖ ^ 2 := by
    have hmem : i ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ i
    have := Finset.single_le_sum (f := fun j : Fin 2 => ‖q j‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem
    simpa [Real.norm_eq_abs] using this
  exact this

/-! ### A regular zero of a `C¹` function is never isolated in the zero set -/

lemma regular_zero_not_isolated (f : R2 → ℝ) (hf : Continuous f) (p : R2)
    (hfp : f p = 0) (hdiff : DifferentiableAt ℝ f p) (hne : fderiv ℝ f p ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) : ∃ q : R2, f q = 0 ∧ q ≠ p ∧ ‖q - p‖ < δ := by
  set L := fderiv ℝ f p with _hLdef
  have hLd : HasFDerivAt f L p := hdiff.hasFDerivAt
  -- a vector `u` with `L u = 1`
  obtain ⟨w, hw⟩ : ∃ w : R2, L w ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by ext w; simp [h w])
  set u : R2 := (L w)⁻¹ • w with hu
  have hLu : L u = 1 := by
    simp only [hu, map_smul, smul_eq_mul]
    field_simp
  -- a nonzero vector `v` in the kernel of `L`
  set v : R2 := (L (E 1)) • E 0 - (L (E 0)) • E 1 with hv
  have hLv : L v = 0 := by simp [hv]; ring
  have hvne : v ≠ 0 := by
    intro h
    have h0 : L (E 1) = 0 := by
      have : v 0 = 0 := by rw [h]; simp
      simpa [hv] using this
    have h1 : L (E 0) = 0 := by
      have : v 1 = 0 := by rw [h]; simp
      simpa [hv] using this
    exact hne (clm_eq_zero L h1 h0)
  -- constants
  set K : ℝ := ‖u‖ + ‖v‖ + 1 with hK
  have hKpos : 0 < K := by
    have := norm_nonneg u; have := norm_nonneg v; simp only [hK]; linarith
  set c : ℝ := 1 / (2 * K) with hc
  have hcpos : 0 < c := by positivity
  -- the little-o estimate
  have hlo := hLd.isLittleO
  have hev : ∀ᶠ x in nhds p, ‖f x - f p - L (x - p)‖ ≤ c * ‖x - p‖ := hlo.def hcpos
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hrpos, hr⟩ := hev
  set ε : ℝ := min (δ / (2 * K)) (r / (2 * K)) with _hε
  have hεpos : 0 < ε := by
    apply lt_min <;> positivity
  have hεK1 : ε * K ≤ δ / 2 := by
    have : ε ≤ δ / (2 * K) := min_le_left _ _
    calc ε * K ≤ (δ / (2 * K)) * K := by nlinarith
      _ = δ / 2 := by field_simp
  have hεK2 : ε * K ≤ r / 2 := by
    have : ε ≤ r / (2 * K) := min_le_right _ _
    calc ε * K ≤ (r / (2 * K)) * K := by nlinarith
      _ = r / 2 := by field_simp
  set t : ℝ := ε / 2 with ht
  have htpos : 0 < t := by positivity
  -- the key estimate along the segment
  have key : ∀ s : ℝ, |s| ≤ ε →
      ‖(p + t • v + s • u) - p‖ ≤ ε * K ∧ |f (p + t • v + s • u) - s| ≤ ε / 2 := by
    intro s _hs
    have hxp : (p + t • v + s • u) - p = t • v + s • u := by abel
    have hnorm : ‖(p + t • v + s • u) - p‖ ≤ ε * K := by
      rw [hxp]
      have h1 : ‖t • v + s • u‖ ≤ |t| * ‖v‖ + |s| * ‖u‖ := by
        refine le_trans (norm_add_le _ _) ?_
        simp [norm_smul, Real.norm_eq_abs]
      have ht' : |t| ≤ ε := by rw [ht, abs_of_pos htpos]; linarith
      have : |t| * ‖v‖ + |s| * ‖u‖ ≤ ε * ‖v‖ + ε * ‖u‖ := by
        have := norm_nonneg v; have := norm_nonneg u
        nlinarith
      have hKge : ε * ‖v‖ + ε * ‖u‖ ≤ ε * K := by
        simp only [hK]; nlinarith [hεpos]
      linarith
    refine ⟨hnorm, ?_⟩
    have hdist : dist (p + t • v + s • u) p < r := by
      rw [dist_eq_norm]
      calc ‖(p + t • v + s • u) - p‖ ≤ ε * K := hnorm
        _ ≤ r / 2 := hεK2
        _ < r := by linarith
    have := hr hdist
    rw [hfp, hxp] at this
    have hLval : L (t • v + s • u) = s := by
      rw [map_add, map_smul, map_smul, hLu, hLv]
      simp
    rw [hLval] at this
    have hb : ‖f (p + t • v + s • u) - 0 - s‖ ≤ c * ‖t • v + s • u‖ := this
    have hnorm' : ‖t • v + s • u‖ ≤ ε * K := by rw [← hxp]; exact hnorm
    have : c * ‖t • v + s • u‖ ≤ c * (ε * K) := by nlinarith [hcpos]
    have hfin : c * (ε * K) = ε / 2 := by
      rw [hc]; field_simp
    have := le_trans hb this
    rw [hfin] at this
    simpa [Real.norm_eq_abs] using this
  -- intermediate value theorem
  have hgcont : ContinuousOn (fun s : ℝ => f (p + t • v + s • u)) (Set.Icc (-ε) ε) := by
    apply Continuous.continuousOn
    exact hf.comp (by continuity)
  have hpos : 0 ≤ f (p + t • v + ε • u) := by
    have := (key ε (by rw [abs_of_pos hεpos])).2
    have := abs_le.mp this
    linarith [this.1]
  have hneg : f (p + t • v + (-ε) • u) ≤ 0 := by
    have := (key (-ε) (by rw [abs_neg, abs_of_pos hεpos])).2
    have := abs_le.mp this
    linarith [this.2]
  have hsub := intermediate_value_Icc (by linarith : (-ε : ℝ) ≤ ε) hgcont
  have h0mem : (0 : ℝ) ∈ Set.Icc (f (p + t • v + (-ε) • u)) (f (p + t • v + ε • u)) :=
    ⟨hneg, hpos⟩
  obtain ⟨s, hsmem, hs0⟩ := hsub h0mem
  refine ⟨p + t • v + s • u, hs0, ?_, ?_⟩
  · intro hcon
    have hxp : (p + t • v + s • u) - p = t • v + s • u := by abel
    have : t • v + s • u = 0 := by rw [← hxp, hcon]; simp
    have hLzero : L (t • v + s • u) = s := by
      rw [map_add, map_smul, map_smul, hLu, hLv]; simp
    rw [this] at hLzero
    simp at hLzero
    rw [← hLzero] at this
    simp at this
    rcases this with h | h
    · exact absurd h (ne_of_gt htpos)
    · exact hvne h
  · have habs : |s| ≤ ε := by
      rw [abs_le]
      exact ⟨hsmem.1, hsmem.2⟩
    have := (key s habs).1
    calc ‖(p + t • v + s • u) - p‖ ≤ ε * K := this
      _ ≤ δ / 2 := hεK1
      _ < δ := by linarith

/-! ### The defining function for `a ∉ {0,1}` -/

/-- The candidate defining function `f a (x,y) = y² - x(x-1)(x-a)`. -/
noncomputable def fa (a : ℝ) : R2 → ℝ := fun q => (q 1) ^ 2 - (q 0) * ((q 0) - 1) * ((q 0) - a)

/-- The differential of `fa a` at `p`. -/
noncomputable def La (a : ℝ) (p : R2) : R2 →L[ℝ] ℝ :=
  (2 * p 1) • P 1 - (3 * (p 0) ^ 2 - 2 * (1 + a) * (p 0) + a) • P 0

lemma fa_contDiff (a : ℝ) : ContDiff ℝ 1 (fa a) := by
  have h0 : ContDiff ℝ 1 (fun q : R2 => q 0) := (P 0).contDiff
  have h1 : ContDiff ℝ 1 (fun q : R2 => q 1) := (P 1).contDiff
  exact (h1.pow 2).sub ((h0.mul (h0.sub contDiff_const)).mul (h0.sub contDiff_const))

lemma fa_hasFDerivAt (a : ℝ) (p : R2) : HasFDerivAt (fa a) (La a p) p := by
  have h0 : HasFDerivAt (fun q : R2 => q 0) (P 0) p := (P 0).hasFDerivAt
  have h1 : HasFDerivAt (fun q : R2 => q 1) (P 1) p := (P 1).hasFDerivAt
  have h := (h1.pow 2).sub ((h0.mul (h0.sub_const 1)).mul (h0.sub_const a))
  convert h using 1
  ext w
  simp [La, P]
  ring

lemma fa_fderiv (a : ℝ) (p : R2) : fderiv ℝ (fa a) p = La a p := (fa_hasFDerivAt a p).fderiv

/-! ### The parametrized curve used for the case `a = 1` -/

/-- `s ↦ (s², s³ - s)` parametrizes the nodal cubic `y² = x(x-1)²`. -/
noncomputable def sig : ℝ → R2 := fun s => (s ^ 2) • E 0 + (s ^ 3 - s) • E 1

@[simp] lemma sig_zero (s : ℝ) : (sig s) 0 = s ^ 2 := by simp [sig]

@[simp] lemma sig_one (s : ℝ) : (sig s) 1 = s ^ 3 - s := by simp [sig]

lemma sig_hasDerivAt (s : ℝ) :
    HasDerivAt sig ((2 * s) • E 0 + (3 * s ^ 2 - 1) • E 1) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
  have h2 : HasDerivAt (fun s : ℝ => s ^ 3 - s) (3 * s ^ 2 - 1) s := by
    have h_sub := (hasDerivAt_pow 3 s).sub (hasDerivAt_id s)
    exact h_sub
  exact (h1.smul_const (E 0)).add (h2.smul_const (E 1))

/-! ### The two impossible cases -/

/-- For `a = 0` the origin is an isolated point of `M 0`, so `M 0` is not a regular level set. -/
lemma not_submanifold_zero :
    ¬ IsEmbeddedSubmanifold { p : R2 | (p 1) ^ 2 = (p 0) * ((p 0) - 1) * ((p 0) - 0) } := by
  rintro ⟨f, hfC, hset, hreg⟩
  have hf : Continuous f := hfC.continuous
  -- the origin lies in `M 0`
  have h0mem : (0 : R2) ∈ { p : R2 | (p 1) ^ 2 = (p 0) * ((p 0) - 1) * ((p 0) - 0) } := by
    simp
  have hf0 : f 0 = 0 := by
    have := hset ▸ h0mem
    simpa using this
  -- the origin is isolated in `M 0`
  have hiso : ∀ q : R2, f q = 0 → ‖q - (0 : R2)‖ < 1 / 2 → q = 0 := by
    intro q hq hqn
    have hqM : (q 1) ^ 2 = (q 0) * ((q 0) - 1) * ((q 0) - 0) := by
      have : q ∈ { p : R2 | f p = 0 } := hq
      rw [← hset] at this
      exact this
    have hq0 : |q 0| ≤ ‖q‖ := abs_coord_le_norm q 0
    have hqn' : ‖q‖ < 1 / 2 := by simpa using hqn
    have hlt : |q 0| < 1 / 2 := lt_of_le_of_lt hq0 hqn'
    have _hx : q 0 - 1 < 0 := by
      have := abs_lt.mp hlt
      linarith [this.2]
    have _h1x : 0 < 1 - q 0 := by linarith
    have key : (q 0) ^ 2 * (1 - q 0) = -(q 1) ^ 2 := by linear_combination hqM
    have hsq : (q 0) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (q 1), sq_nonneg (q 0)]) (sq_nonneg _)
    have hx0 : q 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have _hy0 : q 1 = 0 := by
      have : (q 1) ^ 2 = 0 := by rw [hqM, hx0]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    ext i; fin_cases i <;> simpa
  obtain ⟨q, hq, hqne, hqd⟩ :=
    regular_zero_not_isolated f hf 0 hf0 (hfC.differentiable (by norm_num)).differentiableAt
      (hreg 0 hf0) (by norm_num : (0:ℝ) < 1/2)
  exact hqne (hiso q hq hqd)

/-- For `a = 1` the point `(1,0)` is a node of `M 1`: two smooth branches with independent
tangent directions cross there, so no `C¹` defining function can have nonzero differential. -/
lemma not_submanifold_one :
    ¬ IsEmbeddedSubmanifold { p : R2 | (p 1) ^ 2 = (p 0) * ((p 0) - 1) * ((p 0) - 1) } := by
  rintro ⟨f, hfC, hset, hreg⟩
  set M : Set R2 := { p : R2 | (p 1) ^ 2 = (p 0) * ((p 0) - 1) * ((p 0) - 1) } with hM
  have hcurve : ∀ s : ℝ, f (sig s) = 0 := by
    intro s
    have : sig s ∈ M := by
      simp only [hM, Set.mem_ofPred_eq, sig_zero, sig_one]
      ring
    rw [hset] at this
    exact this
  have hp : f (sig 1) = 0 := hcurve 1
  set L := fderiv ℝ f (sig 1) with _hLdef
  have hLd : HasFDerivAt f L (sig 1) :=
    ((hfC.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  -- derivative along the branch through `s = 1`
  have hd1 : HasDerivAt (fun s : ℝ => f (sig s)) (L ((2 * (1:ℝ)) • E 0 + (3 * (1:ℝ) ^ 2 - 1) • E 1)) 1 :=
    hLd.comp_hasDerivAt 1 (sig_hasDerivAt 1)
  have hzero1 : L ((2 * (1:ℝ)) • E 0 + (3 * (1:ℝ) ^ 2 - 1) • E 1) = 0 := by
    have hconst : (fun s : ℝ => f (sig s)) = fun _ => (0:ℝ) := funext hcurve
    rw [hconst] at hd1
    have := hd1.deriv
    simpa using this.symm
  -- derivative along the branch through `s = -1`
  have hsig : sig (-1 : ℝ) = sig 1 := by
    ext i; fin_cases i <;> norm_num [sig]
  have hLd' : HasFDerivAt f L (sig (-1)) := by rw [hsig]; exact hLd
  have hd2 : HasDerivAt (fun s : ℝ => f (sig s))
      (L ((2 * (-1:ℝ)) • E 0 + (3 * (-1:ℝ) ^ 2 - 1) • E 1)) (-1) :=
    hLd'.comp_hasDerivAt (-1) (sig_hasDerivAt (-1))
  have hzero2 : L ((2 * (-1:ℝ)) • E 0 + (3 * (-1:ℝ) ^ 2 - 1) • E 1) = 0 := by
    have hconst : (fun s : ℝ => f (sig s)) = fun _ => (0:ℝ) := funext hcurve
    rw [hconst] at hd2
    have := hd2.deriv
    simpa using this.symm
  simp only [map_add, map_smul, smul_eq_mul] at hzero1 hzero2
  norm_num at hzero1 hzero2
  have hE0 : L (E 0) = 0 := by linarith
  have hE1 : L (E 1) = 0 := by linarith
  exact hreg (sig 1) hp (clm_eq_zero L hE0 hE1)

end Lee510

open Lee510 in
/-- **Lee, Problem 5-10.** `M a = {(x,y) : y² = x(x-1)(x-a)}` is an embedded submanifold
of `ℝ²` (a regular level set) exactly when `a ≠ 0` and `a ≠ 1`. -/
theorem Lee_5_10 (a : ℝ) :
    let M : Set R2 := { p : R2 | (p 1) ^ 2 = (p 0) * ((p 0) - 1) * ((p 0) - a) }
    IsEmbeddedSubmanifold M ↔ (a ≠ 0 ∧ a ≠ 1) := by
  intro _M
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; exact not_submanifold_zero h
    · rintro rfl; exact not_submanifold_one h
  · rintro ⟨ha0, ha1⟩
    refine ⟨fa a, fa_contDiff a, ?_, ?_⟩
    · ext p
      simp only [Set.mem_ofPred_eq, fa, sub_eq_zero]
      exact Iff.rfl
    · intro p hp
      rw [fa_fderiv]
      intro hL
      -- evaluate the differential on the basis vectors
      have h1 : (La a p) (E 1) = 2 * p 1 := by simp [La, P]
      have h0 : (La a p) (E 0) = -(3 * (p 0) ^ 2 - 2 * (1 + a) * (p 0) + a) := by
        simp [La, P]
      rw [hL] at h1 h0
      simp only [zero_apply] at h1 h0
      have hy : p 1 = 0 := by linarith
      have hq : 3 * (p 0) ^ 2 - 2 * (1 + a) * (p 0) + a = 0 := by linarith
      have hzero : (p 0) * ((p 0) - 1) * ((p 0) - a) = 0 := by
        have : (p 1) ^ 2 - (p 0) * ((p 0) - 1) * ((p 0) - a) = 0 := hp
        rw [hy] at this; linarith [this]
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rw [h'] at hq; simp at hq; exact ha0 hq
        · have hx : p 0 = 1 := by linarith
          rw [hx] at hq
          apply ha1
          linarith
      · have hx : p 0 = a := by linarith
        rw [hx] at hq
        have : a * (a - 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact ha0 h'
        · exact ha1 (by linarith)
