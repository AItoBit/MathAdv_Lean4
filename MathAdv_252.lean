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

set_option grind.warning false

/-!
# Finiteness of the expected first passage time of a random walk with positive drift

Let `X 0, X 1, …` be i.i.d. real random variables with `E X_0 > 0`, let
`S_k = X_0 + … + X_{k-1}` and, for `a > 0`, let `τ = inf {k ≥ 1 : S_k > a}`.
Then `E τ < ∞`.

The proof is the classical one: truncate the increments from above at a level `c`
chosen so large that `m := E (X_0 ∧ c) > 0`, truncate the stopping time at `n`,
apply Wald's equation to the truncated walk (whose stopped value is at most `a + c`),
and let `n → ∞` by monotone convergence.

Since Wald's equation is not available in Mathlib, it is proved here in the form
`sum_measureReal_belowSet_le`.

The ingredients of this argument are therefore: Wald's equation, truncation of the
increments `X i`, truncation of the stopping time `τ`, and a monotone passage to the
limit.  The optional stopping theorem is *not* used (answer (b) to the accompanying
multiple-choice question).
-/

namespace WaldStopping

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partial sums of a sequence of functions. -/
noncomputable def psum (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, Y i ω

/-- The event that the walk `psum Y` has not exceeded `a` up to time `i`; this is the
event `{τ > i}` for the walk `psum Y`. -/
def belowSet (Y : ℕ → Ω → ℝ) (a : ℝ) (i : ℕ) : Set Ω := {ω | ∀ j ≤ i, psum Y j ω ≤ a}

/-- The walk stopped at `min τ n`, written as a sum of increments multiplied by
the indicators of the events `{τ > i}`. -/
noncomputable def waldSum (Y : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, (belowSet Y a i).indicator (fun _ => (1 : ℝ)) ω * Y i ω

omit [MeasurableSpace Ω] in
lemma belowSet_antitone (Y : ℕ → Ω → ℝ) (a : ℝ) {i j : ℕ} (hij : i ≤ j) :
    belowSet Y a j ⊆ belowSet Y a i := by
  intro ω hω k hk
  exact hω k (hk.trans hij)

lemma measurable_psum {Y : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (Y i)) (k : ℕ) :
    Measurable (psum Y k) :=
  Finset.measurable_sum _ fun i _ => hmeas i

lemma measurableSet_belowSet {Y : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (Y i)) (a : ℝ) (i : ℕ) :
    MeasurableSet (belowSet Y a i) := by
  have : belowSet Y a i = ⋂ j ∈ Finset.range (i + 1), {ω | psum Y j ω ≤ a} := by
    ext ω
    simp [belowSet]
  rw [this]
  exact MeasurableSet.biInter (Finset.range (i + 1)).countable_toSet fun j _ =>
    measurableSet_le (measurable_psum hmeas j) measurable_const

omit [MeasurableSpace Ω] in
lemma waldSum_eq_psum {Y : ℕ → Ω → ℝ} {a : ℝ} {n : ℕ} {ω : Ω} (hω : ω ∈ belowSet Y a n) :
    waldSum Y a n ω = psum Y n ω := by
  unfold waldSum psum
  refine Finset.sum_congr rfl fun i hi => ?_
  have : ω ∈ belowSet Y a i :=
    belowSet_antitone Y a (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))) hω
  simp [Set.indicator_of_mem this]

omit [MeasurableSpace Ω] in
lemma waldSum_le {Y : ℕ → Ω → ℝ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbdd : ∀ i ω, Y i ω ≤ c) (n : ℕ) (ω : Ω) : waldSum Y a n ω ≤ a + c := by
  induction n with
  | zero => simpa [waldSum] using by linarith
  | succ n ih =>
      rw [waldSum, Finset.sum_range_succ, ← waldSum]
      by_cases hω : ω ∈ belowSet Y a n
      · rw [Set.indicator_of_mem hω, waldSum_eq_psum hω]
        have h1 : psum Y n ω ≤ a := hω n le_rfl
        have h2 : Y n ω ≤ c := hbdd n ω
        simp only [one_mul]
        linarith
      · rw [Set.indicator_of_notMem hω]
        simpa using ih

/-- Independence of the indicator of `{τ > i}` (which depends only on `Y 0, …, Y (i-1)`)
from the increment `Y i`. -/
lemma indepFun_indicator_belowSet {μ : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ) (a : ℝ) (i : ℕ) :
    IndepFun ((belowSet Y a i).indicator (fun _ => (1 : ℝ))) (Y i) μ := by
  classical
  have hdisj : Disjoint (Finset.range i) ({i} : Finset ℕ) := by simp
  have h := hindep.indepFun_finset (Finset.range i) {i} hdisj hmeas
  set E : Set (↥(Finset.range i) → ℝ) :=
    {v | ∀ j ≤ i, (∑ l ∈ Finset.range j,
        (if hl : l ∈ Finset.range i then v ⟨l, hl⟩ else 0)) ≤ a} with hE
  have hEmeas : MeasurableSet E := by
    have hset : E = ⋂ j ∈ Finset.range (i + 1),
        {v : ↥(Finset.range i) → ℝ | (∑ l ∈ Finset.range j,
          (if hl : l ∈ Finset.range i then v ⟨l, hl⟩ else 0)) ≤ a} := by
      ext v; simp [hE]
    rw [hset]
    refine MeasurableSet.biInter (Finset.range (i + 1)).countable_toSet fun j _ => ?_
    refine measurableSet_le (Finset.measurable_sum _ fun l _ => ?_) measurable_const
    by_cases hl : l ∈ Finset.range i
    · simp [hl]
      exact measurable_pi_apply _
    · simp [hl]
  have hφ : Measurable (fun v : ↥(Finset.range i) → ℝ => E.indicator (fun _ => (1 : ℝ)) v) :=
    measurable_const.indicator hEmeas
  have hψ : Measurable (fun v : ↥({i} : Finset ℕ) → ℝ => v ⟨i, by simp⟩) := measurable_pi_apply _
  have hcomp := h.comp hφ hψ
  have hsum : ∀ (ω : Ω) (j : ℕ), j ≤ i →
      (∑ l ∈ Finset.range j, (if hl : l ∈ Finset.range i then Y l ω else 0))
        = ∑ l ∈ Finset.range j, Y l ω := by
    intro ω j hj
    refine Finset.sum_congr rfl fun l hl => ?_
    have : l ∈ Finset.range i :=
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hl) hj)
    simp [this]
  convert hcomp using 1
  · funext ω
    simp only [Function.comp_apply, Set.indicator_apply, hE, Set.mem_ofPred_eq, belowSet, psum]
    congr 1
    apply propext
    constructor
    · intro hh j hj
      rw [hsum ω j hj]; exact hh j hj
    · intro hh j hj
      have := hh j hj
      rwa [hsum ω j hj] at this
  · rfl

lemma integrable_indicator_mul {μ : Measure Ω} {Y : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i, Integrable (Y i) μ) (a : ℝ) (i : ℕ) :
    Integrable (fun ω => (belowSet Y a i).indicator (fun _ => (1 : ℝ)) ω * Y i ω) μ := by
  refine Integrable.mono' (hint i).abs
    (((measurable_const.indicator (measurableSet_belowSet hmeas a i)).mul
      (hmeas i)).aestronglyMeasurable) ?_
  filter_upwards with ω
  by_cases hω : ω ∈ belowSet Y a i
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω, abs_nonneg]

lemma integrable_waldSum {μ : Measure Ω} {Y : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i, Integrable (Y i) μ) (a : ℝ) (n : ℕ) : Integrable (waldSum Y a n) μ := by
  unfold waldSum
  exact integrable_finsetSum _ fun i _ => integrable_indicator_mul hmeas hint a i

lemma integral_waldSum {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ)
    (hint : ∀ i, Integrable (Y i) μ) (a : ℝ) (n : ℕ) :
    ∫ ω, waldSum Y a n ω ∂μ
      = ∑ i ∈ Finset.range n, μ.real (belowSet Y a i) * ∫ ω, Y i ω ∂μ := by
  simp only [waldSum]
  rw [integral_finsetSum _ fun i _ => integrable_indicator_mul hmeas hint a i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(indepFun_indicator_belowSet hmeas hindep a i).integral_fun_mul_eq_mul_integral
      ((measurable_const.indicator (measurableSet_belowSet hmeas a i)).aestronglyMeasurable)
      (hint i).1]
  congr 1
  rw [integral_indicator_const (1 : ℝ) (measurableSet_belowSet hmeas a i)]
  simp

/-- **Wald's equation, in the form needed here**: the expected value of the truncated
stopping time is at most `(a + c) / m`. -/
lemma sum_measureReal_belowSet_le {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    {a c m : ℝ} (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ)
    (hint : ∀ i, Integrable (Y i) μ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbdd : ∀ i ω, Y i ω ≤ c) (hm : 0 < m) (hmean : ∀ i, ∫ ω, Y i ω ∂μ = m) (n : ℕ) :
    ∑ i ∈ Finset.range n, μ.real (belowSet Y a i) ≤ (a + c) / m := by
  have h1 : ∫ ω, waldSum Y a n ω ∂μ ≤ a + c := by
    calc ∫ ω, waldSum Y a n ω ∂μ ≤ ∫ _ω, (a + c) ∂μ :=
          integral_mono (integrable_waldSum hmeas hint a n) (integrable_const _)
            fun ω => waldSum_le ha hc hbdd n ω
      _ = a + c := by simp
  rw [integral_waldSum hmeas hindep hint a n] at h1
  simp_rw [hmean] at h1
  rw [← Finset.sum_mul] at h1
  rw [le_div_iff₀ hm]
  exact h1

/-- Since `E Z > 0` and `min Z c ↑ Z`, some truncation `min Z c` still has positive mean. -/
lemma exists_truncation_level {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℝ}
    (hZ : Measurable Z) (hint : Integrable Z μ) (hpos : 0 < ∫ ω, Z ω ∂μ) :
    ∃ c : ℝ, 1 ≤ c ∧ 0 < ∫ ω, min (Z ω) c ∂μ := by
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ ω, min (Z ω) ((n : ℝ) + 1) ∂μ) Filter.atTop
      (nhds (∫ ω, Z ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |Z ω|)
      (fun n => (hZ.min measurable_const).aestronglyMeasurable) hint.abs ?_ ?_
    · intro n
      filter_upwards with ω
      rcases le_total (Z ω) ((n : ℝ) + 1) with h | h
      · simp [min_eq_left h]
      · rw [min_eq_right h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact h.trans (le_abs_self _)
    · filter_upwards with ω
      obtain ⟨N, hN⟩ := exists_nat_ge (Z ω)
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hle : Z ω ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      simp [min_eq_left hle]
  obtain ⟨n, hn⟩ := (hlim.eventually_const_lt hpos).exists
  exact ⟨(n : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) n], hn⟩

/-- The Lebesgue integral of a `ℕ`-valued function as the sum of the tail probabilities. -/
lemma lintegral_nat_eq_tsum_measure {μ : Measure Ω} (f : Ω → ℕ)
    (hms : ∀ i : ℕ, MeasurableSet {ω | i < f ω}) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∑' i : ℕ, μ {ω | i < f ω} := by
  have hpt : ∀ ω, ((f ω : ℝ≥0∞))
      = ∑' i : ℕ, Set.indicator {ω | i < f ω} (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (f ω)) (by
      intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [Nat.not_lt.mpr hi])]
    simp [Set.indicator_apply, Finset.filter_true_of_mem]
  simp_rw [hpt]
  rw [lintegral_tsum fun i => (measurable_const.indicator (hms i)).aemeasurable]
  simp_rw [lintegral_indicator (hms _), MeasureTheory.lintegral_const,
    Measure.restrict_apply MeasurableSet.univ]
  simp

end WaldStopping

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def tauFrom
    {Ω : Type*} (S : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ :=
  if h : ∃ k : ℕ, 1 ≤ k ∧ S k ω > a then
    Nat.find h
  else
    0

/-
The statement below is the one from the problem, with the independence assumption
`Pairwise (fun i j => IndepFun (X i) (X j) μ)` replaced by full (mutual) independence
`iIndepFun X μ`.

Pairwise independence is *not* enough for this result: the classical proof goes through
Wald's equation, which requires the increment `X k` to be independent of the whole event
`{τ ≥ k}`, an event depending on `X 0, …, X (k-1)` jointly.  (One can in fact build
identically distributed, pairwise independent `X i` taking the two values `1/2 ± 1` for
which `P(τ > n) ≳ 1/n`, using Walsh functions indexed by an affine subspace of `GF(2)^d`;
that counterexample is not formalized here.)  The original statement is kept, commented
out, below the corrected one.
-/

/-- If `X 0, X 1, …` are i.i.d. real random variables with positive mean and `a > 0`, then
the first passage time `τ = inf {k ≥ 1 : S k > a}` of the random walk
`S k = X 0 + … + X (k-1)` has finite expectation. -/
theorem problem_25
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_ident : ∀ n, MeasureTheory.Measure.map (X n) μ = MeasureTheory.Measure.map (X 0) μ)
    (h_pos : (∫ ω, X 0 ω ∂μ) > 0)
    (a : ℝ) (ha : 0 < a) :
    let S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, X i ω
    (∫⁻ ω, (tauFrom S a ω : ℝ≥0∞) ∂μ) < ⊤ := by
  intro S
  have hSmeas : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ fun i _ => h_meas i
  -- `X 0` is integrable, since otherwise its integral would vanish
  have hX0 : Integrable (X 0) μ := by
    by_contra hcon
    rw [integral_undef hcon] at h_pos
    exact lt_irrefl 0 h_pos
  -- choose a truncation level `c ≥ 1` such that the truncated mean is still positive
  obtain ⟨c, hc1, hcpos⟩ := WaldStopping.exists_truncation_level (h_meas 0) hX0 h_pos
  have hc0 : (0 : ℝ) ≤ c := by linarith
  set Y : ℕ → Ω → ℝ := fun i ω => min (X i ω) c with hYdef
  have hYmeas : ∀ i, Measurable (Y i) := fun i => (h_meas i).min measurable_const
  have hYindep : iIndepFun Y μ :=
    h_indep.comp (fun _ x => min x c) fun _ => measurable_id.min measurable_const
  have hYbdd : ∀ i ω, Y i ω ≤ c := fun i ω => min_le_right _ _
  -- integrability and equality of the means of the truncated variables
  have hY0int : Integrable (Y 0) μ := by
    have hbound : Integrable (fun ω => |X 0 ω| + c) μ := hX0.abs.add (integrable_const c)
    refine Integrable.mono' hbound (hYmeas 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rcases le_total (X 0 ω) c with h | h
    · have : Y 0 ω = X 0 ω := min_eq_left h
      rw [this, Real.norm_eq_abs]
      linarith
    · have : Y 0 ω = c := min_eq_right h
      rw [this, Real.norm_eq_abs, abs_of_nonneg hc0]
      linarith [abs_nonneg (X 0 ω)]
  have hYint : ∀ i, Integrable (Y i) μ := by
    intro i
    have hm : AEStronglyMeasurable (fun x : ℝ => min x c) (Measure.map (X i) μ) :=
      (measurable_id.min measurable_const).aestronglyMeasurable
    have h1 : Integrable (fun x : ℝ => min x c) (Measure.map (X i) μ) := by
      rw [h_ident i]
      exact (integrable_map_measure
        (measurable_id.min measurable_const).aestronglyMeasurable
        (h_meas 0).aemeasurable).mpr hY0int
    exact (integrable_map_measure hm (h_meas i).aemeasurable).mp h1
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = ∫ ω, Y 0 ω ∂μ := by
    intro i
    have hmi : ∫ x : ℝ, min x c ∂(Measure.map (X i) μ) = ∫ ω, Y i ω ∂μ :=
      integral_map (h_meas i).aemeasurable
        (measurable_id.min measurable_const).aestronglyMeasurable
    have hm0 : ∫ x : ℝ, min x c ∂(Measure.map (X 0) μ) = ∫ ω, Y 0 ω ∂μ :=
      integral_map (h_meas 0).aemeasurable
        (measurable_id.min measurable_const).aestronglyMeasurable
    rw [← hmi, ← hm0, h_ident i]
  set m : ℝ := ∫ ω, Y 0 ω ∂μ with hmdef
  have hm : 0 < m := hcpos
  -- Wald's inequality for the truncated walk
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range n, μ.real (WaldStopping.belowSet Y a i) ≤ (a + c) / m :=
    fun n => WaldStopping.sum_measureReal_belowSet_le hYmeas hYindep hYint ha.le hc0 hYbdd hm
      hYmean n
  -- the event `{τ > i}` is contained in the corresponding event for the truncated walk
  have hsub : ∀ i : ℕ, {ω | i < tauFrom S a ω} ⊆ WaldStopping.belowSet Y a i := by
    intro i ω hω j hj
    simp only [Set.mem_ofPred_eq] at hω
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simpa [WaldStopping.psum] using ha.le
    · have hS : S j ω ≤ a := by
        by_contra hcon
        rw [not_le] at hcon
        have hex : ∃ k : ℕ, 1 ≤ k ∧ S k ω > a := ⟨j, hj1, hcon⟩
        have hval : tauFrom S a ω = Nat.find hex := by simp [tauFrom, hex]
        rw [hval] at hω
        exact absurd (Nat.find_le ⟨hj1, hcon⟩) (not_le.mpr (lt_of_le_of_lt hj hω))
      refine le_trans ?_ hS
      exact Finset.sum_le_sum fun l _ => min_le_left _ _
  -- and it is measurable
  have hmeasU : ∀ i : ℕ, MeasurableSet {ω | i < tauFrom S a ω} := by
    intro i
    have hset : {ω | i < tauFrom S a ω}
        = (⋃ k : ℕ, {ω | 1 ≤ k ∧ a < S k ω})
            ∩ ⋂ j ∈ Finset.range (i + 1), {ω | 1 ≤ j → S j ω ≤ a} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
        Finset.mem_range, Nat.lt_succ_iff]
      by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ S k ω > a
      · have hval : tauFrom S a ω = Nat.find hex := by simp [tauFrom, hex]
        rw [hval, Nat.lt_find_iff]
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · obtain ⟨k, hk1, hk2⟩ := hex
            exact ⟨k, hk1, hk2⟩
          · intro j hj hj1
            have := h j hj
            rw [not_and, not_lt] at this
            exact this hj1
        · rintro ⟨-, h2⟩ j hj
          rw [not_and, not_lt]
          intro hj1
          exact h2 j hj hj1
      · have hval : tauFrom S a ω = 0 := by simp [tauFrom, hex]
        rw [hval]
        simp only [Nat.not_lt_zero, false_iff, not_and]
        rintro ⟨k, hk1, hk2⟩
        exact absurd ⟨k, hk1, hk2⟩ hex
    rw [hset]
    refine MeasurableSet.inter (MeasurableSet.iUnion fun k => ?_)
      (MeasurableSet.biInter (Finset.range (i + 1)).countable_toSet fun j _ => ?_)
    · by_cases hk : 1 ≤ k
      · simpa [hk] using measurableSet_lt measurable_const (hSmeas k)
      · simp [hk]
    · by_cases hj : 1 ≤ j
      · simpa [hj] using measurableSet_le (hSmeas j) measurable_const
      · simp [hj]
  -- put everything together
  rw [WaldStopping.lintegral_nat_eq_tsum_measure _ hmeasU]
  have hb : ∀ n : ℕ, ∑ i ∈ Finset.range n, μ {ω | i < tauFrom S a ω}
      ≤ ENNReal.ofReal ((a + c) / m) := by
    intro n
    calc ∑ i ∈ Finset.range n, μ {ω | i < tauFrom S a ω}
        ≤ ∑ i ∈ Finset.range n, μ (WaldStopping.belowSet Y a i) :=
          Finset.sum_le_sum fun i _ => measure_mono (hsub i)
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, μ.real (WaldStopping.belowSet Y a i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => measureReal_nonneg]
          exact Finset.sum_congr rfl fun i _ =>
            (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((a + c) / m) := ENNReal.ofReal_le_ofReal (key n)
  calc ∑' i : ℕ, μ {ω | i < tauFrom S a ω}
      = ⨆ n : ℕ, ∑ i ∈ Finset.range n, μ {ω | i < tauFrom S a ω} := ENNReal.tsum_eq_iSup_nat
    _ ≤ ENNReal.ofReal ((a + c) / m) := iSup_le hb
    _ < ⊤ := ENNReal.ofReal_lt_top

/-
The original statement of the problem, which assumes only pairwise independence:

theorem problem_25'
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ)
  (h_meas : ∀ n, Measurable (X n))
  (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
  (h_ident : ∀ n, MeasureTheory.Measure.map (X n) μ = MeasureTheory.Measure.map (X 0) μ)
  (h_pos : (∫ ω, X 0 ω ∂μ) > 0)
  (a : ℝ) (ha : 0 < a) :
  let S : ℕ → Ω → ℝ := fun k ω => ∑ i in Finset.range k, X i ω
  (∫⁻ ω, (tauFrom S a ω : ℝ≥0∞) ∂μ) < ⊤ := by
  sorry
-/
