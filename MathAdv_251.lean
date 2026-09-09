import Mathlib

/-!
# Convex, decreasing functions vanishing at infinity

For `f` continuous on `ℝ`, convex on `[0,∞)` and tending to `0` at `+∞`, we show that `f` is
antitone and nonnegative on `[0,∞)`, and that minus its right derivative `gfun f` is a
nonnegative, antitone, measurable function with

`∫ s in Ioi t, gfun f s = f t` for every `t ≥ 0`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Polya

/-- Minus the right derivative of `f`. -/
noncomputable def rd (f : ℝ → ℝ) (s : ℝ) : ℝ := -(derivWithin f (Ioi s) s)

/-- A globally measurable modification of `rd f`, agreeing with it on `(0,∞)`. -/
noncomputable def gfun (f : ℝ → ℝ) (s : ℝ) : ℝ := rd f (Real.exp (Real.log s))

variable {f : ℝ → ℝ}

lemma gfun_eq_rd {s : ℝ} (hs : 0 < s) : gfun f s = rd f s := by
  rw [gfun, Real.exp_log hs]

section

variable (h_cont : Continuous f) (h_convex : ConvexOn ℝ (Ici 0) f)
  (h_lim : Tendsto f atTop (𝓝 0))

include h_convex h_lim in
/-- A convex function on `[0,∞)` tending to `0` at infinity is antitone. -/
theorem antitoneOn_of_convex : AntitoneOn f (Ici 0) := by
  intro x hx y hy hxy
  by_contra hcon
  push_neg at hcon
  have hxy' : x < y := lt_of_le_of_ne hxy (by rintro rfl; exact lt_irrefl _ hcon)
  set m : ℝ := (f y - f x) / (y - x) with hm
  have hmpos : 0 < m := div_pos (by linarith) (by linarith)
  have hlb : ∀ z, y < z → f y + m * (z - y) ≤ f z := by
    intro z hz
    have := h_convex.slope_mono_adjacent hx (show z ∈ Ici (0:ℝ) by
      simp only [mem_Ici] at hx ⊢; linarith [hx, hxy'.le, hz.le]) hxy' hz
    rw [← hm] at this
    have hzy : 0 < z - y := by linarith
    rw [le_div_iff₀ hzy] at this
    linarith
  have htop : Tendsto (fun z : ℝ => f y + m * (z - y)) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop hmpos
    exact tendsto_atTop_add_const_right _ _ tendsto_id
  have hftop : Tendsto f atTop atTop := by
    apply tendsto_atTop_mono' atTop _ htop
    filter_upwards [Ioi_mem_atTop y] with z hz using hlb z hz
  exact not_tendsto_nhds_of_tendsto_atTop hftop 0 h_lim

include h_convex h_lim in
theorem nonneg_of_convex {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  refine le_of_tendsto h_lim ?_
  filter_upwards [Ici_mem_atTop x] with y hy
  exact antitoneOn_of_convex h_convex h_lim hx (le_trans hx hy) hy

include h_convex in
lemma hasDerivWithinAt_rd {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt f (-(rd f x)) (Ioi x) x := by
  have hint : x ∈ interior (Ici (0:ℝ)) := by
    rw [interior_Ici]; exact hx
  have := h_convex.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  simpa [rd] using this

include h_convex h_lim in
lemma rd_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ rd f x := by
  have hint : x ∈ interior (Ici (0:ℝ)) := by rw [interior_Ici]; exact hx
  have hslope := h_convex.rightDeriv_le_slope_of_mem_interior hint
    (show x + 1 ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith) (by linarith)
  have hle : f (x + 1) ≤ f x :=
    antitoneOn_of_convex h_convex h_lim (show x ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith)
      (show x + 1 ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith) (by linarith)
  have : slope f x (x + 1) ≤ 0 := by
    rw [slope_def_field, div_nonpos_iff]
    right
    constructor
    · linarith
    · linarith
  rw [rd, neg_nonneg]
  linarith [hslope.trans this]

include h_convex in
lemma rd_antitoneOn : AntitoneOn (rd f) (Ioi 0) := by
  intro x hx y hy hxy
  have hmono := h_convex.monotoneOn_rightDeriv
  rw [interior_Ici] at hmono
  have := hmono hx hy hxy
  simp only [rd]
  linarith

include h_convex h_lim in
lemma gfun_nonneg (s : ℝ) : 0 ≤ gfun f s := by
  rw [gfun]
  exact rd_nonneg h_convex h_lim (Real.exp_pos _)

include h_convex in
lemma gfun_antitoneOn : AntitoneOn (gfun f) (Ioi 0) := by
  intro x hx y hy hxy
  rw [gfun_eq_rd hx, gfun_eq_rd hy]
  exact rd_antitoneOn h_convex hx hy hxy

include h_convex in
lemma gfun_measurable : Measurable (gfun f) := by
  have hH : Antitone (fun x : ℝ => rd f (Real.exp x)) := by
    intro x y hxy
    exact rd_antitoneOn h_convex (Real.exp_pos x) (Real.exp_pos y) (Real.exp_le_exp.2 hxy)
  exact hH.measurable.comp Real.measurable_log

include h_cont h_convex h_lim in
/-- The interval integral of `gfun f`. -/
lemma intervalIntegral_gfun {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) :
    IntegrableOn (gfun f) (Ioc t b) ∧ ∫ x in t..b, gfun f x = f t - f b := by
  have hderiv : ∀ x ∈ Ioo t b, HasDerivWithinAt (fun y => -f y) (gfun f x) (Ioi x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt ht hx.1
    rw [gfun_eq_rd hx0]
    simpa using (hasDerivWithinAt_rd h_convex hx0).neg
  have hpos : ∀ x ∈ Ioo t b, 0 ≤ gfun f x := fun x _ => gfun_nonneg h_convex h_lim x
  have hcont : ContinuousOn (fun y => -f y) (Icc t b) := (h_cont.neg).continuousOn
  have hint : IntegrableOn (gfun f) (Ioc t b) :=
    intervalIntegral.integrableOn_deriv_right_of_nonneg hcont hderiv hpos
  refine ⟨hint, ?_⟩
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htb hcont hderiv
    (by rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htb]; exact hint)
  rw [heq]
  ring

include h_cont h_convex h_lim in
/-- The improper integral of `gfun f` on `(t, ∞)` equals `f t`. -/
theorem integrableOn_gfun {t : ℝ} (ht : 0 ≤ t) : IntegrableOn (gfun f) (Ioi t) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (f t) t ?_ tendsto_id ?_
  · intro b
    rcases le_or_gt t b with h | h
    · exact (intervalIntegral_gfun h_cont h_convex h_lim ht h).1
    · rw [Ioc_eq_empty (by simp; linarith)]
      simp
  · have hcongr : ∀ b : ℝ, t ≤ b → (∫ x in t..b, ‖gfun f x‖) = f t - f b := by
      intro b hb
      rw [← (intervalIntegral_gfun h_cont h_convex h_lim ht hb).2]
      rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
      refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      exact Real.norm_of_nonneg (gfun_nonneg h_convex h_lim x)
    have hlim2 : Tendsto (fun b : ℝ => f t - f b) atTop (𝓝 (f t)) := by
      have := h_lim.const_sub (f t)
      simpa using this
    refine Tendsto.congr' ?_ hlim2
    filter_upwards [Ici_mem_atTop t] with b hb
    exact (hcongr b hb).symm

include h_cont h_convex h_lim in
theorem integral_gfun_Ioi {t : ℝ} (ht : 0 ≤ t) : ∫ s in Ioi t, gfun f s = f t := by
  have hint := integrableOn_gfun h_cont h_convex h_lim ht
  have h1 := intervalIntegral_tendsto_integral_Ioi t hint tendsto_id
  have h2 : Tendsto (fun b : ℝ => ∫ x in t..b, gfun f x) atTop (𝓝 (f t)) := by
    have hlim2 : Tendsto (fun b : ℝ => f t - f b) atTop (𝓝 (f t)) := by
      have := h_lim.const_sub (f t)
      simpa using this
    refine Tendsto.congr' ?_ hlim2
    filter_upwards [Ici_mem_atTop t] with b hb
    exact ((intervalIntegral_gfun h_cont h_convex h_lim ht hb).2).symm
  exact tendsto_nhds_unique h1 h2

end

end Polya
