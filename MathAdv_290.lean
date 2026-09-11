import Mathlib

/-!
# The Riesz Representation Theorem cannot be extended to `p = ∞`

For the Lebesgue measure on a nontrivial closed bounded interval `[a, b]` we show that the
dual space of `L^∞[a,b]` is **not** isometrically isomorphic to `L^1[a,b]`; in other words the
Riesz representation theorem `(L^p)* ≅ L^q` fails at `p = ∞`.

The argument is the classical one:

* `L^1[a,b]` is separable;
* a real normed space whose dual is separable is itself separable
  (`RieszInftyFails.separableSpace_of_separableSpace_dual`, proved via Hahn–Banach);
* `L^∞[a,b]` is *not* separable (`RieszInftyFails.not_separableSpace_LpTop`): the indicator
  functions of the intervals `(-∞, t] `, for `t ∈ (a,b)`, form an uncountable family whose
  mutual distances are all equal to `1`.

Hence `(L^∞[a,b])*` cannot be separable, so it cannot be isometrically isomorphic to
`L^1[a,b]`.
-/

open MeasureTheory TopologicalSpace Set

namespace RieszInftyFails

/-! ### A normed space whose dual is separable is separable -/

/-- **Hahn–Banach**: given a proper closed subspace `Y` of a real normed space and a point
outside of it, there is a norm-one continuous linear functional vanishing on `Y`. -/
theorem exists_norm_one_functional_vanishing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Submodule ℝ E) (hY : IsClosed (Y : Set E)) (x : E) (hx : x ∉ Y) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ y ∈ Y, f y = 0 := by
  obtain ⟨f, u, hfu, hxu⟩ :=
    geometric_hahn_banach_closed_point (s := (Y : Set E)) (x := x) Y.convex hY hx
  have hf0 : ∀ y ∈ Y, f y = 0 := by
    intro y hy
    by_contra hne
    set c : ℝ := (u + 1) / f y with hc
    have hmem : c • y ∈ Y := Y.smul_mem c hy
    have h := hfu _ hmem
    rw [map_smul] at h
    simp only [smul_eq_mul, hc] at h
    rw [div_mul_cancel₀ _ hne] at h
    linarith
  have hfne : f ≠ 0 := by
    intro h
    rw [h] at hfu hxu
    simp only [ContinuousLinearMap.zero_apply] at hfu hxu
    have := hfu 0 Y.zero_mem
    linarith
  refine ⟨‖f‖⁻¹ • f, ?_, ?_⟩
  · rw [norm_smul]
    simp [norm_ne_zero_iff.2 hfne]
  · intro y hy
    simp [hf0 y hy]

/-- If the (topological) dual of a real normed space is separable, then so is the space. -/
theorem separableSpace_of_separableSpace_dual (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SeparableSpace (E →L[ℝ] ℝ)] : SeparableSpace E := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (E →L[ℝ] ℝ)
  -- For every functional pick an almost norming vector in the closed unit ball.
  have hchoice : ∀ f : E →L[ℝ] ℝ, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f‖ / 2 ≤ |f x| := by
    intro f
    rcases eq_or_lt_of_le (norm_nonneg f) with h | h
    · exact ⟨0, by simp, by simp [← h]⟩
    · obtain ⟨x, hx1, hx2⟩ := f.exists_lt_apply_of_lt_opNorm (r := ‖f‖ / 2) (by linarith)
      exact ⟨x, hx1.le, by simpa [Real.norm_eq_abs] using hx2.le⟩
  choose xf hxf1 hxf2 using hchoice
  set S : Set E := xf '' D with hS
  have hScount : S.Countable := hDc.image _
  -- The countable set `S` has dense span.
  have hspan : closure ((Submodule.span ℝ S : Submodule ℝ E) : Set E) = univ := by
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, x ∉ closure ((Submodule.span ℝ S : Submodule ℝ E) : Set E) := by
      by_contra hc
      push_neg at hc
      exact hne (eq_univ_of_forall hc)
    have hxmem : x ∉ (Submodule.span ℝ S).topologicalClosure := fun hc =>
      hx (by rw [← Submodule.topologicalClosure_coe]; exact hc)
    obtain ⟨f, hf1, hf0⟩ := exists_norm_one_functional_vanishing
      (Submodule.span ℝ S).topologicalClosure
      (by rw [Submodule.topologicalClosure_coe]; exact isClosed_closure) x hxmem
    obtain ⟨g, hgD, hgf⟩ := Metric.mem_closure_iff.1 (hDd f) (1 / 4) (by norm_num)
    have hmem : xf g ∈ (Submodule.span ℝ S).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, hgD, rfl⟩)
    have hfx : f (xf g) = 0 := hf0 _ hmem
    have h1 : ‖g‖ / 2 ≤ |g (xf g)| := hxf2 g
    have h2 : |g (xf g)| = |(g - f) (xf g)| := by simp [hfx]
    have h3 : |(g - f) (xf g)| ≤ ‖g - f‖ * ‖xf g‖ := by
      simpa [Real.norm_eq_abs] using (g - f).le_opNorm (xf g)
    have h4 : ‖g - f‖ < 1 / 4 := by rw [← dist_eq_norm, dist_comm]; exact hgf
    have h5 : ‖g‖ / 2 < 1 / 4 :=
      calc ‖g‖ / 2 ≤ |(g - f) (xf g)| := h2 ▸ h1
        _ ≤ ‖g - f‖ * ‖xf g‖ := h3
        _ ≤ ‖g - f‖ * 1 := mul_le_mul_of_nonneg_left (hxf1 g) (norm_nonneg _)
        _ < 1 / 4 := by linarith
    have h6 : ‖f‖ ≤ ‖g‖ + ‖f - g‖ := norm_le_norm_add_norm_sub' f g
    rw [norm_sub_rev, hf1] at h6
    linarith
  have hsep : IsSeparable (univ : Set E) := by
    rw [← hspan]
    exact hScount.isSeparable.span.closure
  exact isSeparable_univ_iff.1 hsep

/-! ### `L^∞[a,b]` is not separable -/

/-- The restriction of the Lebesgue measure to `[a,b]` gives finite mass to any `(-∞, t]`. -/
theorem measure_Iic_restrict_ne_top (a b t : ℝ) :
    (volume.restrict (Icc a b)) (Iic t) ≠ ⊤ := by
  rw [Measure.restrict_apply measurableSet_Iic]
  exact ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne

/-- The element of `L^∞[a,b]` given by the indicator function of `(-∞, t]`. -/
noncomputable def indicatorIic (a b t : ℝ) : Lp ℝ ⊤ (volume.restrict (Icc a b)) :=
  indicatorConstLp ⊤ (measurableSet_Iic (a := t)) (measure_Iic_restrict_ne_top a b t) (1 : ℝ)

/-- Distinct parameters in `(a,b)` give elements of `L^∞[a,b]` at distance exactly `1`. -/
theorem dist_indicatorIic (a b s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s < t) :
    dist (indicatorIic a b s) (indicatorIic a b t) = 1 := by
  have hne : (volume.restrict (Icc a b)) (symmDiff (Iic s) (Iic t)) ≠ 0 := by
    have hsub : Ioc s t ⊆ symmDiff (Iic s) (Iic t) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_Iic, Set.mem_Ioc] at hx ⊢
      exact Or.inr ⟨hx.2, not_le.2 hx.1⟩
    have h2 : (volume.restrict (Icc a b)) (Ioc s t) ≠ 0 := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      have he : Ioc s t ∩ Icc a b = Ioc s t :=
        inter_eq_left.2 fun x hx => ⟨le_of_lt (lt_of_lt_of_le hs.1 hx.1.le), hx.2.trans ht.2.le⟩
      rw [he, Real.volume_Ioc]
      simp [hst]
    exact fun h => h2 (measure_mono_null hsub h)
  have key := edist_indicatorConstLp_eq_enorm (p := ⊤) (c := (1 : ℝ))
    (μ := volume.restrict (Icc a b))
    (hs := measurableSet_Iic (a := s)) (ht := measurableSet_Iic (a := t))
    (hμs := measure_Iic_restrict_ne_top a b s) (hμt := measure_Iic_restrict_ne_top a b t)
  rw [indicatorIic, indicatorIic, dist_edist, key, toReal_enorm,
    norm_indicatorConstLp_top hne, norm_one]

/-- `L^∞` of the Lebesgue measure on a nontrivial interval `[a,b]` is not separable. -/
theorem not_separableSpace_LpTop (a b : ℝ) (hab : a < b) :
    ¬ SeparableSpace (Lp ℝ ⊤ (volume.restrict (Icc a b))) := by
  intro _
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (Lp ℝ ⊤ (volume.restrict (Icc a b)))
  have hchoice : ∀ t : ℝ, ∃ y ∈ D, dist (indicatorIic a b t) y < 1 / 2 := fun t =>
    Metric.mem_closure_iff.1 (hDd (indicatorIic a b t)) (1 / 2) (by norm_num)
  choose g hgD hgdist using hchoice
  have hinj : InjOn g (Ioo a b) := by
    intro s hs t ht hgst
    by_contra hne
    have hdist : dist (indicatorIic a b s) (indicatorIic a b t) = 1 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact dist_indicatorIic a b s t hs ht h
      · rw [dist_comm]; exact dist_indicatorIic a b t s ht hs h
    have : dist (indicatorIic a b s) (indicatorIic a b t) < 1 :=
      calc dist (indicatorIic a b s) (indicatorIic a b t)
          ≤ dist (indicatorIic a b s) (g s) + dist (g s) (indicatorIic a b t) := dist_triangle _ _ _
        _ = dist (indicatorIic a b s) (g s) + dist (indicatorIic a b t) (g t) := by
            rw [hgst, dist_comm (g t)]
        _ < 1 / 2 + 1 / 2 := by
            exact add_lt_add (hgdist s) (hgdist t)
        _ = 1 := by norm_num
    linarith
  have himg : (g '' Ioo a b).Countable := hDc.mono (by rintro _ ⟨t, _, rfl⟩; exact hgD t)
  have hcount : (Ioo a b).Countable := countable_of_injective_of_countable_image hinj himg
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real hab] at hcount
  exact absurd hcount (not_le.2 Cardinal.aleph0_lt_continuum)

/-! ### Main theorem -/

/-- **The Riesz representation theorem fails for `p = ∞`.** For the Lebesgue measure on a
nontrivial closed bounded interval `[a, b]`, the dual of `L^∞[a,b]` is not isometrically
isomorphic to `L^1[a,b]`. -/
theorem real_analysis_25
    (a b : ℝ) (h : a < b) :
    ¬ Nonempty
      (((MeasureTheory.Lp ℝ (⊤ : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b)))
          →L[ℝ] ℝ)
        ≃ₗᵢ[ℝ]
        (MeasureTheory.Lp ℝ (1 : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b)))) := by
  rintro ⟨e⟩
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SeparableSpace (Lp ℝ (1 : ENNReal) (volume.restrict (Icc a b))) := by infer_instance
  haveI : SeparableSpace ((Lp ℝ (⊤ : ENNReal) (volume.restrict (Icc a b))) →L[ℝ] ℝ) :=
    e.symm.toHomeomorph.isDenseEmbedding.separableSpace
  exact not_separableSpace_LpTop a b h
    (separableSpace_of_separableSpace_dual (Lp ℝ (⊤ : ENNReal) (volume.restrict (Icc a b))))

end RieszInftyFails
