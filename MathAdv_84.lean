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
# Essential singularities and segments

If `f` has an essential singularity at `p`, then for every punctured disc `Δ_r(p) ∖ {p}` around
`p` and every non-degenerate segment `[a,b] ⊆ ℂ`, the image `f (Δ_r(p) ∖ {p})` meets `[a,b]`.

The proof does not use the Casorati–Weierstrass theorem literally (density is not enough to meet a
segment, which has empty interior).  Instead we use the classical strengthening of it obtained
by uniformisation of the complement of a segment: if `f` avoided the segment `[a,b]` on a punctured
disc, then

* `q = (f - a)/(f - b)` avoids the ray `(-∞, 0]`, i.e. takes values in the slit plane;
* `s = exp (log q / 2)` is a holomorphic square root of `q` with positive real part;
* `g = (s-1)/(s+1)` is holomorphic with `‖g‖ < 1`, hence bounded, hence (removable singularity
  theorem) has a limit `c` at `p`;
* `f` is recovered from `g` by the rational formula
  `f = (b (1+g)^2 - a (1-g)^2) / (4 g)`, so either `f` has a limit at `p` (if `c ≠ 0`) or
  `‖f‖ → ∞` at `p` (if `c = 0`).

Both alternatives contradict the singularity being essential.
-/

namespace EssSing

open Complex Filter Topology Set

/-- Möbius transformation sending `a ↦ 0` and `b ↦ ∞`. It maps the complement of the segment
`[a,b]` onto the slit plane. -/
noncomputable def mob (a b w : ℂ) : ℂ := (w - a) / (w - b)

/-- A holomorphic square root of `mob a b` on the complement of the segment `[a,b]`. -/
noncomputable def sqrtMob (a b w : ℂ) : ℂ := Complex.exp (2⁻¹ * Complex.log (mob a b w))

/-- Cayley transform of `sqrtMob a b`: it maps the complement of the segment `[a,b]` into the
open unit disc. -/
noncomputable def discMap (a b w : ℂ) : ℂ := (sqrtMob a b w - 1) / (sqrtMob a b w + 1)

/-- The rational function inverting `discMap a b`. -/
noncomputable def discInv (a b w : ℂ) : ℂ := (b * (1 + w) ^ 2 - a * (1 - w) ^ 2) / (4 * w)

variable {a b w : ℂ}

lemma ne_left_of_not_mem_segment (hw : w ∉ segment ℝ a b) : w ≠ a := by
  rintro rfl; exact hw (left_mem_segment ℝ w b)

lemma ne_right_of_not_mem_segment (hw : w ∉ segment ℝ a b) : w ≠ b := by
  rintro rfl; exact hw (right_mem_segment ℝ a w)

lemma mob_ne_zero (hw : w ∉ segment ℝ a b) : mob a b w ≠ 0 := by
  have h1 : w - a ≠ 0 := sub_ne_zero.2 (ne_left_of_not_mem_segment hw)
  have h2 : w - b ≠ 0 := sub_ne_zero.2 (ne_right_of_not_mem_segment hw)
  exact div_ne_zero h1 h2

lemma mob_ne_one (hab : a ≠ b) (hw : w ∉ segment ℝ a b) : mob a b w ≠ 1 := by
  have h2 : w - b ≠ 0 := sub_ne_zero.2 (ne_right_of_not_mem_segment hw)
  intro h
  rw [mob, div_eq_one_iff_eq h2] at h
  exact hab (by linear_combination -h)

lemma mob_mem_slitPlane (hw : w ∉ segment ℝ a b) : mob a b w ∈ Complex.slitPlane := by
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  have hwb : w - b ≠ 0 := sub_ne_zero.2 (ne_right_of_not_mem_segment hw)
  have hqe : w - a = mob a b w * (w - b) := by
    simp only [mob]; field_simp
  set t : ℝ := (mob a b w).re with ht
  have hqt : mob a b w = (t : ℂ) := Complex.ext (by simp [ht]) (by simp [him])
  rw [hqt] at hqe
  have ht0 : t ≤ 0 := hre
  have ht1 : (0:ℝ) < 1 - t := by linarith
  have ht1' : (1 - (t:ℂ)) ≠ 0 := by
    intro h
    apply ne_of_gt ht1
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  refine hw ⟨1/(1-t), -t/(1-t), by positivity, div_nonneg (by linarith) (by linarith),
    by field_simp; ring, ?_⟩
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp
  linear_combination -hqe

lemma sqrtMob_sq (hw : w ∉ segment ℝ a b) : (sqrtMob a b w) ^ 2 = mob a b w := by
  have h : Complex.exp (2⁻¹ * Complex.log (mob a b w)) ^ 2
      = Complex.exp (Complex.log (mob a b w)) := by
    rw [← Complex.exp_nat_mul]
    ring_nf
  rw [sqrtMob, h, Complex.exp_log (mob_ne_zero hw)]

lemma sqrtMob_re_pos (hw : w ∉ segment ℝ a b) : 0 < (sqrtMob a b w).re := by
  have hz := mob_mem_slitPlane hw
  set z := mob a b w
  have h1 := Complex.neg_pi_lt_arg z
  have h3' : z.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)
  rw [sqrtMob, Complex.exp_re]
  have him : (2⁻¹ * Complex.log z).im = z.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  rw [him]
  have hcos : 0 < Real.cos (z.arg / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith
  positivity

lemma sqrtMob_add_one_ne_zero (hw : w ∉ segment ℝ a b) : sqrtMob a b w + 1 ≠ 0 := by
  intro h
  have hpos := sqrtMob_re_pos hw
  have h' := congrArg Complex.re h
  simp at h'
  linarith

lemma sqrtMob_ne_one (hab : a ≠ b) (hw : w ∉ segment ℝ a b) : sqrtMob a b w ≠ 1 := by
  intro h
  exact mob_ne_one hab hw (by rw [← sqrtMob_sq hw, h]; ring)

lemma discMap_norm_lt_one (hw : w ∉ segment ℝ a b) : ‖discMap a b w‖ < 1 := by
  have hs := sqrtMob_re_pos hw
  set s := sqrtMob a b w
  have h1 : s + 1 ≠ 0 := sqrtMob_add_one_ne_zero hw
  rw [discMap, norm_div, div_lt_one (by positivity)]
  have key : ‖s - 1‖ ^ 2 < ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    nlinarith [hs]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) key

lemma discMap_ne_zero (hab : a ≠ b) (hw : w ∉ segment ℝ a b) : discMap a b w ≠ 0 := by
  rw [discMap, div_ne_zero_iff]
  exact ⟨sub_ne_zero.2 (sqrtMob_ne_one hab hw), sqrtMob_add_one_ne_zero hw⟩

lemma discInv_discMap (hab : a ≠ b) (hw : w ∉ segment ℝ a b) :
    discInv a b (discMap a b w) = w := by
  have hwb : w - b ≠ 0 := sub_ne_zero.2 (ne_right_of_not_mem_segment hw)
  have hsq := sqrtMob_sq hw
  have hs1 : sqrtMob a b w + 1 ≠ 0 := sqrtMob_add_one_ne_zero hw
  have hsm1 : sqrtMob a b w - 1 ≠ 0 := sub_ne_zero.2 (sqrtMob_ne_one hab hw)
  set s := sqrtMob a b w
  have hs2 : s ^ 2 * (w - b) = w - a := by
    rw [hsq, mob, div_mul_cancel₀ _ hwb]
  have hne : s ^ 2 - 1 ≠ 0 := by
    intro h
    rcases mul_eq_zero.1 (show (s - 1) * (s + 1) = 0 by linear_combination h) with h' | h'
    · exact hsm1 h'
    · exact hs1 h'
  rw [discInv, discMap]
  have key : (b * (1 + (s - 1) / (s + 1)) ^ 2 - a * (1 - (s - 1) / (s + 1)) ^ 2)
      / (4 * ((s - 1) / (s + 1))) = (b * s ^ 2 - a) / (s ^ 2 - 1) := by
    field_simp
    ring
  rw [key, div_eq_iff hne]
  linear_combination -hs2

lemma discMap_differentiableAt (hw : w ∉ segment ℝ a b) :
    DifferentiableAt ℂ (discMap a b) w := by
  have hwb : w - b ≠ 0 := sub_ne_zero.2 (ne_right_of_not_mem_segment hw)
  have hslit := mob_mem_slitPlane hw
  have hmob : DifferentiableAt ℂ (mob a b) w :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) hwb
  have hs : DifferentiableAt ℂ (sqrtMob a b) w :=
    Complex.differentiableAt_exp.comp w
      (((Complex.differentiableAt_log hslit).comp w hmob).const_mul _)
  exact DifferentiableAt.div (hs.sub_const 1) (hs.add_const 1) (sqrtMob_add_one_ne_zero hw)

/-- Key step: a holomorphic function on a punctured disc avoiding a non-degenerate segment
either has a limit at the puncture, or tends to infinity there. -/
theorem tendsto_or_tendsto_norm_atTop_of_avoids_segment
    {p : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hab : a ≠ b)
    (hf : DifferentiableOn ℂ f (Metric.ball p r \ {p}))
    (havoid : ∀ z ∈ Metric.ball p r \ {p}, f z ∉ segment ℝ a b) :
    (∃ c : ℂ, Filter.Tendsto f (𝓝[≠] p) (𝓝 c)) ∨
      Filter.Tendsto (fun z => ‖f z‖) (𝓝[≠] p) Filter.atTop := by
  set G : ℂ → ℂ := fun z => discMap a b (f z) with hGdef
  have hball : Metric.ball p r ∈ 𝓝 p := Metric.ball_mem_nhds p hr
  have hev : ∀ᶠ z in 𝓝[≠] p, z ∈ Metric.ball p r \ {p} := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz1 hz2
    exact ⟨hz2, hz1⟩
  have hopen : IsOpen (Metric.ball p r \ {p}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hGd : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ G z := by
    filter_upwards [hev] with z hz
    have hfz : DifferentiableAt ℂ f z := (hf z hz).differentiableAt (hopen.mem_nhds hz)
    exact (discMap_differentiableAt (havoid z hz)).comp z hfz
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] p) fun z => ‖G z - G p‖ := by
    refine ⟨1 + ‖G p‖, Filter.eventually_map.2 ?_⟩
    filter_upwards [hev] with z hz
    calc ‖G z - G p‖ ≤ ‖G z‖ + ‖G p‖ := norm_sub_le _ _
      _ ≤ 1 + ‖G p‖ := by
          gcongr
          exact (discMap_norm_lt_one (havoid z hz)).le
  obtain ⟨c, hlim⟩ : ∃ c : ℂ, Filter.Tendsto G (𝓝[≠] p) (𝓝 c) :=
    ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hGd hbdd⟩
  have hfeq : ∀ᶠ z in 𝓝[≠] p, f z = discInv a b (G z) := by
    filter_upwards [hev] with z hz
    exact (discInv_discMap hab (havoid z hz)).symm
  by_cases hc : c = 0
  · right
    have hnum : Filter.Tendsto (fun z => b * (1 + G z) ^ 2 - a * (1 - G z) ^ 2) (𝓝[≠] p)
        (𝓝 (b - a)) := by
      have hcont : Continuous fun v : ℂ => b * (1 + v) ^ 2 - a * (1 - v) ^ 2 := by fun_prop
      have h := (hcont.continuousAt (x := c)).tendsto.comp hlim
      simpa [Function.comp_def, hc] using h
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hden : Filter.Tendsto (fun z => 4 * G z) (𝓝[≠] p) (𝓝 0) := by
      simp only [hGdef]
      simpa [hc] using hlim.const_mul (4 : ℂ)
    have hinv : ∀ᶠ z in 𝓝[≠] p,
        (f z)⁻¹ = (4 * G z) / (b * (1 + G z) ^ 2 - a * (1 - G z) ^ 2) := by
      filter_upwards [hfeq] with z hz
      rw [hz, discInv, inv_div]
    have hGne : ∀ᶠ z in 𝓝[≠] p, G z ≠ 0 := by
      filter_upwards [hev] with z hz
      exact discMap_ne_zero hab (havoid z hz)
    have hu : Filter.Tendsto (fun z => (f z)⁻¹) (𝓝[≠] p) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h : Filter.Tendsto (fun z => (4 * G z) / (b * (1 + G z) ^ 2 - a * (1 - G z) ^ 2))
            (𝓝[≠] p) (𝓝 (0 / (b - a))) := hden.div hnum hba
        rw [zero_div] at h
        exact h.congr' (Filter.EventuallyEq.symm hinv)
      · filter_upwards [hinv, hGne, hnum.eventually_ne hba] with z h1 h2 h3
        rw [h1]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact div_ne_zero (by simpa using h2) h3
    have h := tendsto_norm_inv_nhdsNE_zero_atTop.comp hu
    simpa [Function.comp_def] using h
  · left
    refine ⟨discInv a b c, ?_⟩
    have hcont : ContinuousAt (discInv a b) c := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · simpa using hc
    exact (hcont.tendsto.comp hlim).congr' (Filter.EventuallyEq.symm hfeq)

/-- `f` has an essential singularity at `p`: it neither has a (finite) limit at `p`, nor tends
to infinity at `p`. -/
def EssentialSingularityAt (f : ℂ → ℂ) (p : ℂ) : Prop :=
  ¬ (∃ c : ℂ, Filter.Tendsto f (𝓝[≠] p) (𝓝 c)) ∧
    ¬ Filter.Tendsto (fun z => ‖f z‖) (𝓝[≠] p) Filter.atTop

/-- **Main theorem.**  If `f` is holomorphic on `U \ {p}` with an essential singularity at `p`,
then for every disc `Δ_r(p) ⊆ U` and every non-degenerate segment `[a,b] ⊆ ℂ`, the image
`f (Δ_r(p) \ {p})` meets `[a,b]`.

The hypothesis `a ≠ b` is necessary: the image can omit a single point, e.g. `exp (1/z)` never
takes the value `0` — see `not_forall_image_punctured_ball_inter_segment_nonempty` below.
The hypotheses `hU : IsOpen U` and `hp : p ∈ U`, kept from the original statement, turn out not
to be needed. -/
theorem image_punctured_ball_inter_segment_nonempty
    (U : Set ℂ) (p : ℂ) (f : ℂ → ℂ)
    (hU : IsOpen U) (hp : p ∈ U)
    (hhol : DifferentiableOn ℂ f (U \ {p}))
    (hess : EssentialSingularityAt f p) :
    ∀ (r : ℝ), 0 < r → Metric.ball p r ⊆ U →
      ∀ (a b : ℂ), a ≠ b →
        ((Set.image f (Metric.ball p r \ {p})) ∩ (segment ℝ a b)) ≠ ∅ := by
  intro r hr hsub a b hab hempty
  have havoid : ∀ z ∈ Metric.ball p r \ {p}, f z ∉ segment ℝ a b := by
    intro z hz hmem
    have hmem' : f z ∈ (Set.image f (Metric.ball p r \ {p})) ∩ (segment ℝ a b) :=
      ⟨⟨z, hz, rfl⟩, hmem⟩
    rw [hempty] at hmem'
    exact hmem'
  have hf : DifferentiableOn ℂ f (Metric.ball p r \ {p}) :=
    hhol.mono (fun z hz => ⟨hsub hz.1, hz.2⟩)
  rcases tendsto_or_tendsto_norm_atTop_of_avoids_segment hr hab hf havoid with h | h
  · exact hess.1 h
  · exact hess.2 h

/-!
### The hypothesis `a ≠ b` cannot be dropped

`exp (1/z)` has an essential singularity at `0` but never takes the value `0`, so its image of
any punctured disc around `0` misses the degenerate segment `[0,0] = {0}`.
-/

lemma tendsto_ofReal_div_natSucc (s : ℝ) (hs : s ≠ 0) :
    Filter.Tendsto (fun n : ℕ => ((s / (n + 1) : ℝ) : ℂ)) Filter.atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Filter.Tendsto (fun n : ℕ => (s / (n + 1) : ℝ)) Filter.atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h
  · filter_upwards with n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero, div_eq_zero_iff]
    push_neg
    exact ⟨hs, by positivity⟩

lemma norm_exp_inv_ofReal_div_natSucc (s : ℝ) (n : ℕ) :
    ‖Complex.exp (((s / (n + 1) : ℝ) : ℂ))⁻¹‖ = Real.exp ((n + 1) / s) := by
  rw [← Complex.ofReal_inv, Complex.norm_exp, Complex.ofReal_re, inv_div]

/-- `z ↦ exp (1/z)` has an essential singularity at `0`. -/
theorem exp_inv_essentialSingularityAt :
    EssentialSingularityAt (fun z : ℂ => Complex.exp z⁻¹) 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h := (hc.comp (tendsto_ofReal_div_natSucc 1 one_ne_zero)).norm
    have h2 : Filter.Tendsto
        (fun n : ℕ => ‖Complex.exp (((1 / (n + 1) : ℝ) : ℂ))⁻¹‖) Filter.atTop Filter.atTop := by
      simp only [norm_exp_inv_ofReal_div_natSucc, div_one]
      exact Real.tendsto_exp_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact not_tendsto_nhds_of_tendsto_atTop h2 ‖c‖ (by simpa [Function.comp_def] using h)
  · intro h
    have h2 := h.comp (tendsto_ofReal_div_natSucc (-1) (by norm_num))
    obtain ⟨n, hn⟩ := (h2.eventually_ge_atTop 2).exists
    rw [Function.comp_apply, norm_exp_inv_ofReal_div_natSucc] at hn
    have hle : Real.exp (((n : ℝ) + 1) / (-1 : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_neg, neg_nonpos]
      linarith
    linarith

lemma exp_inv_differentiableOn (U : Set ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => Complex.exp z⁻¹) (U \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz.2
  exact (Complex.differentiableAt_exp.comp z (differentiableAt_inv hz0)).differentiableWithinAt

/-- For degenerate segments the conclusion genuinely fails: `exp (1/z)` omits the value `0`. -/
theorem exp_inv_image_inter_segment_self_eq_empty (r : ℝ) :
    ((fun z : ℂ => Complex.exp z⁻¹) '' (Metric.ball (0:ℂ) r \ {0})) ∩ segment ℝ 0 0 = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_image, segment_same, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨z, -, rfl⟩
  exact Complex.exp_ne_zero _

/-- The hypothesis `a ≠ b` in `image_punctured_ball_inter_segment_nonempty` cannot be removed. -/
theorem not_forall_image_punctured_ball_inter_segment_nonempty :
    ¬ ∀ (U : Set ℂ) (p : ℂ) (f : ℂ → ℂ), IsOpen U → p ∈ U → DifferentiableOn ℂ f (U \ {p}) →
      EssentialSingularityAt f p → ∀ r : ℝ, 0 < r → Metric.ball p r ⊆ U → ∀ a b : ℂ,
        ((Set.image f (Metric.ball p r \ {p})) ∩ (segment ℝ a b)) ≠ ∅ := by
  intro H
  exact H Set.univ 0 (fun z : ℂ => Complex.exp z⁻¹) isOpen_univ (Set.mem_univ _)
    (exp_inv_differentiableOn Set.univ) exp_inv_essentialSingularityAt 1 one_pos
    (Set.subset_univ _) 0 0 (exp_inv_image_inter_segment_self_eq_empty 1)

/-
The statement as originally posed, without the hypothesis that the singularity is essential and
without `a ≠ b`, is false:

theorem question_10
    (U : Set ℂ) (p : ℂ) (f : ℂ → ℂ)
    (hU : IsOpen U) (hp : p ∈ U)
    (hhol : DifferentiableOn ℂ f (U \ {p})) :
    ∀ (r : ℝ), 0 < r → Metric.ball p r ⊆ U →
      ∀ (a b : ℂ),
        (Set.image f (Metric.ball p r \ {p})) ∩ (segment ℝ a b) ≠ ∅

Indeed the constant function `f = 0` is holomorphic on `U \ {p}` and its image misses the
segment `[1,2]`; and even for a genuine essential singularity the conclusion fails for a
degenerate segment `a = b`, by `not_forall_image_punctured_ball_inter_segment_nonempty` above.
The corrected statement is `image_punctured_ball_inter_segment_nonempty`.
-/

end EssSing
