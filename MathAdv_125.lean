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

open MeasureTheory Filter Topology

namespace Melrose

/-- The truncation in space of `f` to the interval `[-L, L]`. -/
noncomputable def gL (f : ℝ → ℝ) (L x : ℝ) : ℝ := if |x| ≤ L then f x else 0

/-- The truncation in value of `gL f L` at height `N`. -/
noncomputable def gLN (f : ℝ → ℝ) (L N x : ℝ) : ℝ :=
  if gL f L x ≤ -N then -N else if gL f L x ≥ N then N else gL f L x

lemma gL_sq_apply (f : ℝ → ℝ) (L x : ℝ) :
    (gL f L x) ^ 2 = Set.indicator {y : ℝ | |y| ≤ L} (fun y => (f y) ^ 2) x := by
  unfold gL
  by_cases h : |x| ≤ L <;> simp [h]

lemma measurableSet_abs_le (L : ℝ) : MeasurableSet {y : ℝ | |y| ≤ L} :=
  measurableSet_le (by fun_prop) measurable_const

/-- `g_L^2` is integrable. -/
lemma integrable_gL_sq (f : ℝ → ℝ)
    (hf2 : Integrable (fun x : ℝ => (f x) ^ 2) volume) (L : ℝ) :
    Integrable (fun x : ℝ => (gL f L x) ^ 2) volume := by
  have h := hf2.indicator (measurableSet_abs_le L)
  have heq : (fun x : ℝ => (gL f L x) ^ 2)
      = Set.indicator {y : ℝ | |y| ≤ L} (fun y => (f y) ^ 2) := funext (gL_sq_apply f L)
  rw [heq]
  exact h

lemma gL_sq_le (f : ℝ → ℝ) (L x : ℝ) : (gL f L x) ^ 2 ≤ (f x) ^ 2 := by
  unfold gL
  by_cases h : |x| ≤ L <;> simp [h, sq_nonneg]

/-- For nonnegative heights the truncation is the usual clamp. -/
lemma gLN_eq_clamp (f : ℝ → ℝ) (L N x : ℝ) (hN : 0 ≤ N) :
    gLN f L N x = max (-N) (min N (gL f L x)) := by
  unfold gLN
  set t := gL f L x with ht
  by_cases h1 : t ≤ -N
  · have h2 : t ≤ N := le_trans h1 (by linarith)
    simp [h1, min_eq_right h2]
  · push_neg at h1
    by_cases h2 : t ≥ N
    · simp [h1.not_ge, h2, max_eq_right (by linarith : -N ≤ N)]
    · push_neg at h2
      simp [h1.not_ge, h2.not_ge, min_eq_right h2.le, max_eq_right h1.le]

lemma aestronglyMeasurable_gL (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume) (L : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => gL f L x) volume := by
  have : (fun x : ℝ => gL f L x)
      = Set.indicator {y : ℝ | |y| ≤ L} (fun y => f y) := by
    funext x
    unfold gL
    by_cases h : |x| ≤ L <;> simp [h]
  rw [this]
  exact hf.indicator (measurableSet_abs_le L)

lemma aestronglyMeasurable_gLN (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (L N : ℝ) (hN : 0 ≤ N) :
    AEStronglyMeasurable (fun x : ℝ => gLN f L N x) volume := by
  have heq : (fun x : ℝ => gLN f L N x)
      = fun x : ℝ => max (-N) (min N (gL f L x)) :=
    funext fun x => gLN_eq_clamp f L N x hN
  rw [heq]
  have hg := aestronglyMeasurable_gL f hf L
  fun_prop

lemma abs_gLN_le (f : ℝ → ℝ) (L N x : ℝ) (hN : 0 ≤ N) :
    |gLN f L N x| ≤ |gL f L x| := by
  rw [gLN_eq_clamp f L N x hN]
  set t := gL f L x
  rcases le_total t (-N) with h | h
  · have : max (-N) (min N t) = -N := by
      have h2 : t ≤ N := le_trans h (by linarith)
      simp [min_eq_right h2, max_eq_left h]
    rw [this, abs_neg, abs_of_nonneg hN]
    have : -t ≥ N := by linarith
    calc N ≤ -t := this
      _ ≤ |t| := neg_le_abs t
  · rcases le_total N t with h2 | h2
    · have : max (-N) (min N t) = N := by
        simp [min_eq_left h2, max_eq_right (by linarith : -N ≤ N)]
      rw [this, abs_of_nonneg hN]
      exact le_trans h2 (le_abs_self t)
    · have : max (-N) (min N t) = t := by
        simp [min_eq_right h2, max_eq_right h]
      rw [this]

/-- Pointwise bound for the value-truncation error. -/
lemma abs_gLN_sq_sub_gL_sq_le (f : ℝ → ℝ) (L N x : ℝ) (hN : 0 ≤ N) :
    |(gLN f L N x) ^ 2 - (gL f L x) ^ 2| ≤ (f x) ^ 2 := by
  have h1 : (gLN f L N x) ^ 2 ≤ (gL f L x) ^ 2 := by
    have := abs_gLN_le f L N x hN
    calc (gLN f L N x) ^ 2 = |gLN f L N x| ^ 2 := (sq_abs _).symm
      _ ≤ |gL f L x| ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (gL f L x) ^ 2 := sq_abs _
  have h2 : (0 : ℝ) ≤ (gLN f L N x) ^ 2 := sq_nonneg _
  have h3 := gL_sq_le f L x
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- For fixed `x`, the value truncation is eventually exact. -/
lemma eventually_gLN_eq (f : ℝ → ℝ) (L x : ℝ) :
    ∀ᶠ N : ℝ in atTop, gLN f L N x = gL f L x := by
  filter_upwards [eventually_gt_atTop |gL f L x|] with N hN
  have hNpos : 0 ≤ N := le_trans (abs_nonneg _) hN.le
  have h1 : ¬ (gL f L x ≤ -N) := by
    have := neg_abs_le (gL f L x); push_neg; linarith
  have h2 : ¬ (gL f L x ≥ N) := by
    have := le_abs_self (gL f L x); push_neg; linarith
  unfold gLN
  simp [h1, h2]

/-- For fixed `x`, the space truncation is eventually exact. -/
lemma eventually_gL_eq (f : ℝ → ℝ) (x : ℝ) :
    ∀ᶠ L : ℝ in atTop, gL f L x = f x := by
  filter_upwards [eventually_ge_atTop |x|] with L hL
  unfold gL
  simp [hL]

/-- Convergence of the value-truncated squares, for fixed `L`. -/
lemma tendsto_integral_gLN (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hf2 : Integrable (fun x : ℝ => (f x) ^ 2) volume) (L : ℝ) :
    Tendsto (fun N : ℝ => ∫ x : ℝ, |(gLN f L N x) ^ 2 - (gL f L x) ^ 2| ∂volume)
      atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) ∂volume := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (f x) ^ 2) ?_ ?_ hf2 ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    have h1 := aestronglyMeasurable_gLN f hf L N hN
    have h2 := aestronglyMeasurable_gL f hf L
    fun_prop
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_gLN_sq_sub_gL_sq_le f L N x hN
  · filter_upwards with x
    have hev : (fun _ : ℝ => (0 : ℝ))
        =ᶠ[atTop] fun N : ℝ => |(gLN f L N x) ^ 2 - (gL f L x) ^ 2| := by
      filter_upwards [eventually_gLN_eq f L x] with N hN
      simp [hN]
    exact Tendsto.congr' hev tendsto_const_nhds

/-- Convergence of the space-truncated squares. -/
lemma tendsto_integral_gL (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hf2 : Integrable (fun x : ℝ => (f x) ^ 2) volume) :
    Tendsto (fun L : ℝ => ∫ x : ℝ, |(gL f L x) ^ 2 - (f x) ^ 2| ∂volume)
      atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) ∂volume := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (f x) ^ 2) ?_ ?_ hf2 ?_
  · filter_upwards with L
    have h2 := aestronglyMeasurable_gL f hf L
    fun_prop
  · filter_upwards with L
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := gL_sq_le f L x
    have h2 : (0 : ℝ) ≤ (gL f L x) ^ 2 := sq_nonneg _
    rw [abs_of_nonpos (by linarith)]
    linarith
  · filter_upwards with x
    have hev : (fun _ : ℝ => (0 : ℝ))
        =ᶠ[atTop] fun L : ℝ => |(gL f L x) ^ 2 - (f x) ^ 2| := by
      filter_upwards [eventually_gL_eq f x] with L hL
      simp [hL]
    exact Tendsto.congr' hev tendsto_const_nhds

end Melrose

/-- **Melrose, Spring 2009, Problem 5.**  For `f` locally integrable with `f^2` integrable,
the space truncations `g_L` have integrable square, the value truncations `g_L^{(N)}` converge
to `g_L` in the relevant `L^1` sense as `N → ∞`, and `g_L^2 → f^2` in `L^1` as `L → ∞`.
All three limits are instances of the Lebesgue dominated convergence theorem. -/
theorem melrose_sp2009_5
  (f : ℝ → ℝ)
  (h_loc :
    ∀ x : ℝ,
      ∃ (ε : ℝ), 0 < ε ∧ MeasureTheory.IntegrableOn f (Metric.ball x ε) volume)
  (h_sq_int : MeasureTheory.Integrable (fun x : ℝ ↦ (f x)^2) volume) :
  (let
      gL (L x : ℝ) : ℝ :=
        if |x| ≤ L then f x else 0
    let
      gL_N (L N x : ℝ) : ℝ :=
        if gL L x ≤ -N then -N
        else if gL L x ≥ N then N
        else gL L x
    (∀ L > 0, MeasureTheory.Integrable (fun x ↦ (gL L x)^2) volume) ∧
    (∀ L > 0,
        Filter.Tendsto (fun N ↦ ∫ x, |(gL_N L N x)^2 - (gL L x)^2| ∂volume)
          Filter.atTop (𝓝 0)) ∧
    Filter.Tendsto (fun L ↦ ∫ x, |(gL L x)^2 - (f x)^2| ∂volume)
      Filter.atTop (𝓝 0)) := by
  have hlocint : LocallyIntegrable f volume := by
    intro x
    obtain ⟨ε, hε, h⟩ := h_loc x
    exact ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, h⟩
  have hf : AEStronglyMeasurable f volume := hlocint.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · intro L _
    exact Melrose.integrable_gL_sq f h_sq_int L
  · intro L _
    exact Melrose.tendsto_integral_gLN f hf h_sq_int L
  · exact Melrose.tendsto_integral_gL f hf h_sq_int
