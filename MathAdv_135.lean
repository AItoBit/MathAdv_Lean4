import Mathlib

/-!
# A smooth function all of whose derivatives eventually vanish at each point is a polynomial

Let `f : ℝ → ℝ` be infinitely differentiable and suppose that for every `x ∈ ℝ` there is a `k_x`
with `f⁽ᵏ⁾(x) = 0` for all `k ≥ k_x`.  Then `f` is a polynomial.

The proof is the classical one, based on the **Baire category theorem** (answer (a) to the
accompanying multiple-choice question): the set of points near which `f` is not a polynomial is a
closed subset of `ℝ`, hence a complete metric space, and it is covered by the countably many
closed sets on which a fixed derivative vanishes.
-/

open Set Filter Topology
open scoped ContDiff

namespace SmoothLocallyPoly

/-- `f` is a polynomial near `x`: some iterated derivative of `f` vanishes identically on a
neighbourhood of `x`. -/
def IsPolyNear (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ n : ℕ, ∀ᶠ y in 𝓝 x, iteratedDeriv n f y = 0

/-- The set of points near which `f` is not a polynomial. -/
def badSet (f : ℝ → ℝ) : Set ℝ := {x | ¬ IsPolyNear f x}

variable {f g : ℝ → ℝ}

/-! ### Basic facts about iterated derivatives -/

theorem contDiff_iteratedDeriv (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact hf.iterate_deriv n

theorem differentiable_iteratedDeriv (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n f) :=
  (contDiff_iteratedDeriv hf n).differentiable (by simp)

theorem iteratedDeriv_add_apply (n m : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (n + m) f = iteratedDeriv n (iteratedDeriv m f) := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- If `g` vanishes on an open set `U`, so do all its iterated derivatives. -/
theorem iteratedDeriv_eq_zero_of_eqZero_on_open {U : Set ℝ} (hU : IsOpen U) :
    ∀ (j : ℕ) (g : ℝ → ℝ), (∀ x ∈ U, g x = 0) → ∀ x ∈ U, iteratedDeriv j g x = 0 := by
  intro j
  induction j with
  | zero => intro g hg x hx; simpa using hg x hx
  | succ j ih =>
    intro g hg x hx
    rw [iteratedDeriv_succ']
    refine ih (deriv g) ?_ x hx
    intro y hy
    have : deriv g y = deriv (fun _ => (0:ℝ)) y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hU.mem_nhds hy] with z hz using hg z hz
    simpa using this

/-- Monotonicity: if the `m`-th derivative vanishes on an open set, so does the `k`-th for
`k ≥ m`. -/
theorem iteratedDeriv_eq_zero_of_le {U : Set ℝ} (hU : IsOpen U) {m : ℕ}
    (hm : ∀ x ∈ U, iteratedDeriv m f x = 0) {k : ℕ} (hk : m ≤ k) :
    ∀ x ∈ U, iteratedDeriv k f x = 0 := by
  intro x hx
  have hkm : k = (k - m) + m := by omega
  rw [hkm, iteratedDeriv_add_apply]
  exact iteratedDeriv_eq_zero_of_eqZero_on_open hU (k - m) _ hm x hx

/-- If some iterated derivative of `g` vanishes on an open preconnected set `U`, and `g` itself
vanishes on a nonempty open subset of `U`, then `g` vanishes on all of `U`. -/
theorem eqZero_of_iteratedDeriv_eqZero {U V : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty) :
    ∀ (k : ℕ) (g : ℝ → ℝ), ContDiff ℝ ∞ g → (∀ x ∈ U, iteratedDeriv k g x = 0) →
      (∀ x ∈ V, g x = 0) → ∀ x ∈ U, g x = 0 := by
  intro k
  induction k with
  | zero => intro g _ hk _ x hx; simpa using hk x hx
  | succ k ih =>
    intro g hg hk hgV x hx
    have hd : ContDiff ℝ ∞ (deriv g) := by
      rw [show deriv g = iteratedDeriv 1 g by simp [iteratedDeriv_one], iteratedDeriv_eq_iterate]
      exact hg.iterate_deriv 1
    have hdV : ∀ y ∈ V, deriv g y = 0 := by
      intro y hy
      have : deriv g y = deriv (fun _ => (0:ℝ)) y := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hV.mem_nhds hy] with z hz using hgV z hz
      simpa using this
    have hdU : ∀ y ∈ U, deriv g y = 0 := by
      refine ih (deriv g) hd ?_ hdV
      intro y hy
      have := hk y hy
      rwa [iteratedDeriv_succ'] at this
    obtain ⟨v, hv⟩ := hVne
    have hconst : g x = g v :=
      hU.is_const_of_deriv_eq_zero hUc (hg.differentiable (by simp)).differentiableOn
        (fun y hy => hdU y hy) hx (hVU hv)
    rw [hconst, hgV v hv]

/-! ### Locally polynomial on an interval implies polynomial on the interval -/

/-- If `f` is polynomial near every point of an open interval, then a single iterated derivative
of `f` vanishes identically on that interval. -/
theorem exists_iteratedDeriv_eq_zero_of_isPolyNear (hf : ContDiff ℝ ∞ f) {a b : ℝ}
    (h : ∀ x ∈ Ioo a b, IsPolyNear f x) :
    ∃ m : ℕ, ∀ x ∈ Ioo a b, iteratedDeriv m f x = 0 := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨c, hc⟩
  · exact ⟨0, by simp [he]⟩
  obtain ⟨m, hm⟩ := h c hc
  set S : Set ℝ := {x : ℝ | ∀ᶠ y in 𝓝 x, iteratedDeriv m f y = 0} with hSdef
  have hSopen : IsOpen S := isOpen_setOf_eventually_nhds
  have hne : (Ioo a b ∩ S).Nonempty := ⟨c, hc, hm⟩
  have hclos : closure S ∩ Ioo a b ⊆ S := by
    rintro x ⟨hxcl, hxI⟩
    obtain ⟨m', hm'⟩ := h x hxI
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hm'
    set W : Set ℝ := Metric.ball x ε with hW
    have hWopen : IsOpen W := Metric.isOpen_ball
    have hWm' : ∀ y ∈ W, iteratedDeriv m' f y = 0 := fun y hy => hball (by simpa [hW] using hy)
    have hmW : ∀ y ∈ W, iteratedDeriv m f y = 0 := by
      rcases le_or_gt m m' with hle | hlt
      · -- use the connectedness lemma on the ball
        obtain ⟨z, hzS, hzd⟩ := Metric.mem_closure_iff.1 hxcl ε hε
        have hzW : z ∈ W := by simpa [hW, Metric.mem_ball, dist_comm] using hzd
        obtain ⟨δ, hδ, hballz⟩ := Metric.eventually_nhds_iff.1 hzS
        set V : Set ℝ := W ∩ Metric.ball z δ with hV
        have hVopen : IsOpen V := hWopen.inter Metric.isOpen_ball
        have hVne : V.Nonempty := ⟨z, hzW, Metric.mem_ball_self hδ⟩
        have hVm : ∀ y ∈ V, iteratedDeriv m f y = 0 := fun y hy =>
          hballz (by simpa [Metric.mem_ball] using hy.2)
        refine eqZero_of_iteratedDeriv_eqZero hWopen (convex_ball x ε).isPreconnected hVopen
          inter_subset_left hVne (m' - m) (iteratedDeriv m f) (contDiff_iteratedDeriv hf m)
          ?_ hVm
        intro y hy
        rw [← iteratedDeriv_add_apply]
        have : m' - m + m = m' := by omega
        rw [this]
        exact hWm' y hy
      · exact iteratedDeriv_eq_zero_of_le hWopen hWm' (le_of_lt hlt)
    exact Filter.eventually_of_mem (hWopen.mem_nhds (Metric.mem_ball_self hε)) hmW
  have hsub := (isPreconnected_Ioo (a := a) (b := b)).subset_of_closure_inter_subset hSopen hne
    hclos
  exact ⟨m, fun x hx => (hsub hx).self_of_nhds⟩

/-! ### The bad set -/

theorem isOpen_isPolyNear : IsOpen {x : ℝ | IsPolyNear f x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨n, hn⟩
  filter_upwards [eventually_eventually_nhds.2 hn] with y hy
  exact ⟨n, hy⟩

theorem isClosed_badSet : IsClosed (badSet f) := by
  simpa [badSet, ← isOpen_compl_iff, compl_setOf] using (isOpen_isPolyNear (f := f))

/-- The bad set has no isolated points. -/
theorem badSet_no_isolated (hf : ContDiff ℝ ∞ f) {x : ℝ} (hx : x ∈ badSet f) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ badSet f, y ≠ x ∧ |y - x| < ε := by
  by_contra hcon
  push_neg at hcon
  have hleft : ∀ z ∈ Ioo (x - ε) x, IsPolyNear f z := by
    intro z hz
    by_contra hzp
    have h1 : |z - x| < ε := abs_lt.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact absurd h1 (not_lt.2 (hcon z hzp (ne_of_lt hz.2)))
  have hright : ∀ z ∈ Ioo x (x + ε), IsPolyNear f z := by
    intro z hz
    by_contra hzp
    have h1 : |z - x| < ε := abs_lt.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact absurd h1 (not_lt.2 (hcon z hzp (ne_of_gt hz.1)))
  obtain ⟨m₁, hm₁⟩ := exists_iteratedDeriv_eq_zero_of_isPolyNear hf hleft
  obtain ⟨m₂, hm₂⟩ := exists_iteratedDeriv_eq_zero_of_isPolyNear hf hright
  set m := max m₁ m₂ with hm
  have hL : ∀ y ∈ Ioo (x - ε) x, iteratedDeriv m f y = 0 :=
    iteratedDeriv_eq_zero_of_le isOpen_Ioo hm₁ (le_max_left _ _)
  have hR : ∀ y ∈ Ioo x (x + ε), iteratedDeriv m f y = 0 :=
    iteratedDeriv_eq_zero_of_le isOpen_Ioo hm₂ (le_max_right _ _)
  have hclosed : IsClosed {y : ℝ | iteratedDeriv m f y = 0} :=
    isClosed_eq (contDiff_iteratedDeriv hf m).continuous continuous_const
  have hxc : x ∈ closure (Ioo (x - ε) x) := by
    rw [closure_Ioo (by linarith : x - ε ≠ x)]
    exact ⟨by linarith, le_rfl⟩
  have hzero_x : iteratedDeriv m f x = 0 :=
    (hclosed.closure_subset_iff.2 (fun y hy => hL y hy)) hxc
  refine hx ⟨m, ?_⟩
  have hnhd : Ioo (x - ε) (x + ε) ∈ 𝓝 x := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  filter_upwards [hnhd] with y hy
  rcases lt_trichotomy y x with h | h | h
  · exact hL y ⟨hy.1, h⟩
  · rw [h]; exact hzero_x
  · exact hR y ⟨h, hy.2⟩

/-! ### The Baire step -/

theorem exists_baire_interval (hf : ContDiff ℝ ∞ f)
    (hvanish : ∀ x : ℝ, ∃ k : ℕ, ∀ n ≥ k, iteratedDeriv n f x = 0) (hne : (badSet f).Nonempty) :
    ∃ (n : ℕ) (x₀ : ℝ) (r : ℝ), 0 < r ∧ x₀ ∈ badSet f ∧
      ∀ y ∈ badSet f, |y - x₀| < r → iteratedDeriv n f y = 0 := by
  have hcl : IsClosed (badSet f) := isClosed_badSet
  haveI : CompleteSpace (badSet f) := hcl.completeSpace_coe
  haveI : Nonempty (badSet f) := hne.to_subtype
  set A : ℕ → Set (badSet f) := fun n => {z | iteratedDeriv n f z.1 = 0} with hA
  have hAclosed : ∀ n, IsClosed (A n) := fun n =>
    isClosed_eq ((contDiff_iteratedDeriv hf n).continuous.comp continuous_subtype_val)
      continuous_const
  have hcover : (⋃ n, A n) = univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨k, hk⟩ := hvanish z.1
    exact ⟨k, hk k le_rfl⟩
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hAclosed hcover
  obtain ⟨z, hz⟩ := hn
  have hmem : A n ∈ 𝓝 z := mem_interior_iff_mem_nhds.1 hz
  obtain ⟨u, hu, husub⟩ := (mem_nhds_subtype (badSet f) z (A n)).1 hmem
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hu
  refine ⟨n, z.1, r, hr, z.2, ?_⟩
  intro y hy hyr
  have hyu : y ∈ u := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hyr)
  exact husub (show (⟨y, hy⟩ : badSet f) ∈ Subtype.val ⁻¹' u from hyu)

/-- If `g` vanishes on a set `S` which accumulates at `y ∈ S`, then `deriv g y = 0`. -/
theorem deriv_eq_zero_of_accumulation {S : Set ℝ} {y : ℝ} (hg : Differentiable ℝ g)
    (hgS : ∀ z ∈ S, g z = 0) (hy : y ∈ S) (hacc : (𝓝[S \ {y}] y).NeBot) : deriv g y = 0 := by
  haveI := hacc
  have h1 : Tendsto (slope g y) (𝓝[≠] y) (𝓝 (deriv g y)) :=
    hasDerivAt_iff_tendsto_slope.1 (hg y).hasDerivAt
  have h2 : Tendsto (slope g y) (𝓝[S \ {y}] y) (𝓝 (deriv g y)) :=
    h1.mono_left (nhdsWithin_mono _ (fun z hz => hz.2))
  have h3 : Tendsto (slope g y) (𝓝[S \ {y}] y) (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℝ)))
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [slope_def_field, hgS z hz.1, hgS y hy]
  exact tendsto_nhds_unique h2 h3

/-- All higher derivatives vanish on the piece of the bad set given by the Baire step. -/
theorem iteratedDeriv_eq_zero_on_badSet (hf : ContDiff ℝ ∞ f) {n : ℕ} {x₀ r : ℝ}
    (hn : ∀ y ∈ badSet f, |y - x₀| < r → iteratedDeriv n f y = 0) :
    ∀ k, n ≤ k → ∀ y ∈ badSet f, |y - x₀| < r → iteratedDeriv k f y = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hn
  | succ k hk ih =>
    intro y hy hyr
    set S : Set ℝ := {z | z ∈ badSet f ∧ |z - x₀| < r} with hS
    have hyS : y ∈ S := ⟨hy, hyr⟩
    have hacc : (𝓝[S \ {y}] y).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨z, hz, hzy, hzd⟩ :=
        badSet_no_isolated hf hy (lt_min hε (by simp only [sub_pos]; linarith [hyr] : 0 < r - |y - x₀|))
      refine ⟨z, ⟨⟨hz, ?_⟩, ?_⟩, ?_⟩
      · have h1 : |z - x₀| ≤ |z - y| + |y - x₀| := by
          simpa using abs_sub_le z y x₀
        have h2 : |z - y| < r - |y - x₀| := lt_of_lt_of_le hzd (min_le_right _ _)
        linarith
      · simpa using hzy
      · have : |z - y| < ε := lt_of_lt_of_le hzd (min_le_left _ _)
        rw [Real.dist_eq, abs_sub_comm]
        exact this
    rw [iteratedDeriv_succ]
    exact deriv_eq_zero_of_accumulation (differentiable_iteratedDeriv hf k)
      (fun z hz => ih z hz.1 hz.2) hyS hacc

/-- Descending step at the right endpoint of a gap. -/
theorem vanish_on_Ioo_of_right_endpoint (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) {n m : ℕ}
    (hnm : n ≤ m) (hm : ∀ x ∈ Ioo a b, iteratedDeriv m f x = 0)
    (hend : ∀ k, n ≤ k → iteratedDeriv k f b = 0) :
    ∀ x ∈ Ioo a b, iteratedDeriv n f x = 0 := by
  have key : ∀ j : ℕ, j ≤ m - n → ∀ x ∈ Ioo a b, iteratedDeriv (m - j) f x = 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using hm
    | succ j ih =>
      intro hj x hx
      have hstep : ∀ y ∈ Ioo a b, iteratedDeriv (m - j) f y = 0 := ih (by omega)
      have hk1 : (m - (j+1)) + 1 = m - j := by omega
      have hderiv : ∀ y ∈ Ioo a b, deriv (iteratedDeriv (m - (j+1)) f) y = 0 := by
        intro y hy
        have h0 := hstep y hy
        rw [← hk1, iteratedDeriv_succ] at h0
        exact h0
      obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
        (differentiable_iteratedDeriv hf (m - (j+1))).differentiableOn (fun y hy => hderiv y hy)
      have hclosed : IsClosed {y : ℝ | iteratedDeriv (m - (j+1)) f y = c} :=
        isClosed_eq (contDiff_iteratedDeriv hf (m - (j+1))).continuous continuous_const
      have hbcl : b ∈ closure (Ioo a b) := by
        rw [closure_Ioo (ne_of_lt hab)]; exact ⟨le_of_lt hab, le_rfl⟩
      have hbc : iteratedDeriv (m - (j+1)) f b = c :=
        (hclosed.closure_subset_iff.2 (fun y hy => hc y hy)) hbcl
      have hc0 : c = 0 := by rw [← hbc]; exact hend _ (by omega)
      rw [hc x hx, hc0]
  have hfin := key (m - n) le_rfl
  have hmn : m - (m - n) = n := by omega
  rwa [hmn] at hfin

/-- Descending step at the left endpoint of a gap. -/
theorem vanish_on_Ioo_of_left_endpoint (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) {n m : ℕ}
    (hnm : n ≤ m) (hm : ∀ x ∈ Ioo a b, iteratedDeriv m f x = 0)
    (hend : ∀ k, n ≤ k → iteratedDeriv k f a = 0) :
    ∀ x ∈ Ioo a b, iteratedDeriv n f x = 0 := by
  have key : ∀ j : ℕ, j ≤ m - n → ∀ x ∈ Ioo a b, iteratedDeriv (m - j) f x = 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using hm
    | succ j ih =>
      intro hj x hx
      have hstep : ∀ y ∈ Ioo a b, iteratedDeriv (m - j) f y = 0 := ih (by omega)
      have hk1 : (m - (j+1)) + 1 = m - j := by omega
      have hderiv : ∀ y ∈ Ioo a b, deriv (iteratedDeriv (m - (j+1)) f) y = 0 := by
        intro y hy
        have h0 := hstep y hy
        rw [← hk1, iteratedDeriv_succ] at h0
        exact h0
      obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
        (differentiable_iteratedDeriv hf (m - (j+1))).differentiableOn (fun y hy => hderiv y hy)
      have hclosed : IsClosed {y : ℝ | iteratedDeriv (m - (j+1)) f y = c} :=
        isClosed_eq (contDiff_iteratedDeriv hf (m - (j+1))).continuous continuous_const
      have hacl : a ∈ closure (Ioo a b) := by
        rw [closure_Ioo (ne_of_lt hab)]; exact ⟨le_rfl, le_of_lt hab⟩
      have hac : iteratedDeriv (m - (j+1)) f a = c :=
        (hclosed.closure_subset_iff.2 (fun y hy => hc y hy)) hacl
      have hc0 : c = 0 := by rw [← hac]; exact hend _ (by omega)
      rw [hc x hx, hc0]
  have hfin := key (m - n) le_rfl
  have hmn : m - (m - n) = n := by omega
  rwa [hmn] at hfin

/-- The bad set is empty. -/
theorem badSet_eq_empty (hf : ContDiff ℝ ∞ f)
    (hvanish : ∀ x : ℝ, ∃ k : ℕ, ∀ n ≥ k, iteratedDeriv n f x = 0) : badSet f = ∅ := by
  by_contra hne'
  obtain ⟨n, x₀, r, hr, hx₀, hn⟩ :=
    exists_baire_interval hf hvanish (nonempty_iff_ne_empty.2 hne')
  have hall : ∀ k, n ≤ k → ∀ y ∈ badSet f, |y - x₀| < r → iteratedDeriv k f y = 0 :=
    iteratedDeriv_eq_zero_on_badSet hf hn
  have hclosed := isClosed_badSet (f := f)
  have key : ∀ y, |y - x₀| < r → iteratedDeriv n f y = 0 := by
    intro y hy
    by_cases hyb : y ∈ badSet f
    · exact hn y hyb hy
    obtain ⟨hy1, hy2⟩ := abs_lt.1 hy
    obtain ⟨δ, hδ, hballδ⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl y hyb
    have hnotbad : ∀ z : ℝ, |z - y| < δ → z ∉ badSet f := by
      intro z hz
      exact hballδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hz)
    rcases lt_trichotomy y x₀ with hlt | heq | hgt
    · set T : Set ℝ := badSet f ∩ Icc y x₀ with hT
      have hTne : T.Nonempty := ⟨x₀, hx₀, ⟨le_of_lt hlt, le_rfl⟩⟩
      have hTcl : IsClosed T := hclosed.inter isClosed_Icc
      have hTbdd : BddBelow T := ⟨y, fun z hz => hz.2.1⟩
      have hbT : sInf T ∈ T := hTcl.csInf_mem hTne hTbdd
      set b := sInf T with hb
      have hbbad : b ∈ badSet f := hbT.1
      have hyb' : y < b := lt_of_le_of_ne hbT.2.1 (by rintro h; exact hyb (h ▸ hbbad))
      have hgap : ∀ z ∈ Ioo (y - δ) b, IsPolyNear f z := by
        intro z hz
        by_contra hzp
        rcases le_or_gt z y with hzy | hzy
        · exact hnotbad z (abs_lt.2 ⟨by linarith [hz.1], by linarith⟩) hzp
        · have hzT : z ∈ T := ⟨hzp, ⟨le_of_lt hzy, le_trans (le_of_lt hz.2) hbT.2.2⟩⟩
          exact absurd (csInf_le hTbdd hzT) (not_le.2 hz.2)
      obtain ⟨m, hm⟩ := exists_iteratedDeriv_eq_zero_of_isPolyNear hf hgap
      have hm' : ∀ x ∈ Ioo (y - δ) b, iteratedDeriv (max m n) f x = 0 :=
        iteratedDeriv_eq_zero_of_le isOpen_Ioo hm (le_max_left _ _)
      have hbr : |b - x₀| < r := by
        have h1 : y ≤ b := hbT.2.1
        have h2 : b ≤ x₀ := hbT.2.2
        rw [abs_lt]; constructor <;> linarith
      have hend : ∀ k, n ≤ k → iteratedDeriv k f b = 0 := fun k hk => hall k hk b hbbad hbr
      exact vanish_on_Ioo_of_right_endpoint hf (by linarith : y - δ < b) (le_max_right m n) hm'
        hend y ⟨by linarith, hyb'⟩
    · exact absurd (heq ▸ hx₀) hyb
    · set T : Set ℝ := badSet f ∩ Icc x₀ y with hT
      have hTne : T.Nonempty := ⟨x₀, hx₀, ⟨le_rfl, le_of_lt hgt⟩⟩
      have hTcl : IsClosed T := hclosed.inter isClosed_Icc
      have hTbdd : BddAbove T := ⟨y, fun z hz => hz.2.2⟩
      have haT : sSup T ∈ T := hTcl.csSup_mem hTne hTbdd
      set a := sSup T with ha
      have habad : a ∈ badSet f := haT.1
      have hay : a < y := lt_of_le_of_ne haT.2.2 (by rintro h; exact hyb (h ▸ habad))
      have hgap : ∀ z ∈ Ioo a (y + δ), IsPolyNear f z := by
        intro z hz
        by_contra hzp
        rcases lt_or_ge z y with hzy | hzy
        · have hzT : z ∈ T := ⟨hzp, ⟨le_trans haT.2.1 (le_of_lt hz.1), le_of_lt hzy⟩⟩
          exact absurd (le_csSup hTbdd hzT) (not_le.2 hz.1)
        · exact hnotbad z (abs_lt.2 ⟨by linarith, by linarith [hz.2]⟩) hzp
      obtain ⟨m, hm⟩ := exists_iteratedDeriv_eq_zero_of_isPolyNear hf hgap
      have hm' : ∀ x ∈ Ioo a (y + δ), iteratedDeriv (max m n) f x = 0 :=
        iteratedDeriv_eq_zero_of_le isOpen_Ioo hm (le_max_left _ _)
      have har : |a - x₀| < r := by
        have h1 : x₀ ≤ a := haT.2.1
        have h2 : a ≤ y := haT.2.2
        rw [abs_lt]; constructor <;> linarith
      have hend : ∀ k, n ≤ k → iteratedDeriv k f a = 0 := fun k hk => hall k hk a habad har
      exact vanish_on_Ioo_of_left_endpoint hf (by linarith : a < y + δ) (le_max_right m n) hm'
        hend y ⟨hay, by linarith⟩
  refine absurd ⟨n, ?_⟩ hx₀
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with y hy
  exact key y (by rw [← Real.dist_eq]; simpa [Metric.mem_ball] using hy)

/-! ### From vanishing derivative to polynomials -/

theorem exists_polynomial_derivative (q : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, Polynomial.derivative Q = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp; obtain ⟨Q, hQ⟩ := hq; exact ⟨P + Q, by simp [hP, hQ]⟩
  | monomial n c =>
      refine ⟨Polynomial.monomial (n+1) (c / (n+1)), ?_⟩
      rw [Polynomial.derivative_monomial]
      have : ((n:ℝ)+1) ≠ 0 := by positivity
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      congr 1
      field_simp

/-- A smooth function with vanishing `N`-th derivative on an open interval agrees with a
polynomial there. -/
theorem exists_poly_of_iteratedDeriv_eq_zero {a b : ℝ} (N : ℕ) :
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → (∀ x ∈ Ioo a b, iteratedDeriv N g x = 0) →
      ∃ p : Polynomial ℝ, ∀ x ∈ Ioo a b, g x = p.eval x := by
  induction N with
  | zero => intro g _ h; exact ⟨0, by intro x hx; simpa using h x hx⟩
  | succ N ih =>
    intro g hg h
    have hd : ContDiff ℝ ∞ (deriv g) := by
      rw [show deriv g = iteratedDeriv 1 g by simp [iteratedDeriv_one], iteratedDeriv_eq_iterate]
      exact hg.iterate_deriv 1
    obtain ⟨q, hq⟩ := ih (deriv g) hd (by simpa [iteratedDeriv_succ'] using h)
    obtain ⟨Q, hQ⟩ := exists_polynomial_derivative q
    set F : ℝ → ℝ := fun x => g x - Q.eval x with hF
    have hFd : Differentiable ℝ F :=
      (hg.differentiable (by simp)).sub (Polynomial.differentiable Q)
    have hderiv : EqOn (deriv F) 0 (Ioo a b) := by
      intro x hx
      have h1 : deriv F x = deriv g x - deriv (fun y => Q.eval y) x :=
        deriv_sub ((hg.differentiable (by simp)) x) (Polynomial.differentiable Q x)
      rw [h1, Polynomial.deriv, hQ, ← hq x hx]
      simp
    obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      hFd.differentiableOn hderiv
    refine ⟨Q + Polynomial.C c, ?_⟩
    intro x hx
    have hx' := hc x hx
    simp only [hF] at hx'
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    linarith

/-- **Main theorem** (`C^∞` version). -/
theorem isPolynomial_of_iteratedDeriv_eventually_zero (hf : ContDiff ℝ ∞ f)
    (hvanish : ∀ x : ℝ, ∃ k : ℕ, ∀ n ≥ k, iteratedDeriv n f x = 0) :
    ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x := by
  have hbad : badSet f = ∅ := badSet_eq_empty hf hvanish
  have hpoly : ∀ x : ℝ, IsPolyNear f x := by
    intro x
    by_contra hx
    have : x ∈ badSet f := hx
    rw [hbad] at this
    exact this
  have hR : ∀ R : ℝ, ∃ p : Polynomial ℝ, ∀ x ∈ Ioo (-R) R, f x = p.eval x := by
    intro R
    obtain ⟨m, hm⟩ :=
      exists_iteratedDeriv_eq_zero_of_isPolyNear (a := -R) (b := R) hf (fun x _ => hpoly x)
    exact exists_poly_of_iteratedDeriv_eq_zero m f hf hm
  obtain ⟨p, hp⟩ := hR 1
  refine ⟨p, fun x => ?_⟩
  obtain ⟨q, hq⟩ := hR (|x| + 1)
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {z : ℝ | p.eval z = q.eval z} := by
    intro z hz
    have hz' : z ∈ Ioo (-(|x| + 1)) (|x| + 1) := by
      have h0 : (0:ℝ) ≤ |x| := abs_nonneg x
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have h1 := hp z hz
    have h2 := hq z hz'
    simp only [mem_setOf_eq]
    rw [← h1, ← h2]
  have hpq : p = q :=
    Polynomial.eq_of_infinite_eval_eq p q (Set.Infinite.mono hsub (Set.Ioo_infinite (by norm_num)))
  rw [hpq]
  refine hq x ⟨?_, ?_⟩
  · have := neg_abs_le x; linarith
  · have := le_abs_self x; linarith

end SmoothLocallyPoly

/-- **Bollobás, Linear Analysis, Problem 5.15.**
An infinitely differentiable function `f : ℝ → ℝ` such that for every `x` all but finitely many
derivatives of `f` vanish at `x` is a polynomial. -/
theorem bollobas_5_15
    (f : ℝ → ℝ)
    (hf : ContDiff ℝ ⊤ f)
    (hvanish : ∀ x : ℝ, ∃ k : ℕ, ∀ n ≥ k, iteratedDeriv n f x = 0) :
    ∃ p : Polynomial ℝ, ∀ x, f x = p.eval x :=
  SmoothLocallyPoly.isPolynomial_of_iteratedDeriv_eventually_zero (hf.of_le le_top) hvanish
