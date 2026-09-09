import Mathlib

-- # Brownian motion is almost surely unbounded above
-- Let `B` be a standard Brownian motion.  We show that
-- `ℙ (limsup_{t → ∞} B t = ∞) = 1`.
-- Two forms of the conclusion are proved:
-- * `BrownianLimsup.brownian_unbounded_above`: almost surely, for every `M : ℝ` there is a time
--   `t ≥ 0` with `B t > M`;
-- * `BrownianLimsup.brownian_limsup_atTop_eq_top`: almost surely,
--   `limsup_{t → ∞} (B t : EReal) = ⊤`, which is the literal reading of the statement.
-- Mathlib does not contain a construction of Brownian motion, so the defining properties of a
-- standard Brownian motion are taken as hypotheses, packaged in the structure
-- `BrownianLimsup.IsStandardBrownianMotion`.

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Set
open scoped NNReal ENNReal

namespace BrownianLimsup

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `IsStandardBrownianMotion μ B` says that the process `B : ℝ → Ω → ℝ` on the probability space
`(Ω, μ)` is a standard Brownian motion: each `B t` is measurable, `B 0 = 0` a.s., the increment
`B t - B s` is centered Gaussian with variance `t - s`, the increments along any nondecreasing
sequence of times are independent, and almost every path is continuous. -/
structure IsStandardBrownianMotion (μ : Measure Ω) (B : ℝ → Ω → ℝ) : Prop where
  measurable : ∀ t : ℝ, Measurable (B t)
  init : ∀ᵐ ω ∂μ, B 0 ω = 0
  gaussian_increments : ∀ s t : ℝ, s ≤ t →
      μ.map (fun ω => B t ω - B s ω) = gaussianReal 0 (Real.toNNReal (t - s))
  indep_increments : ∀ u : ℕ → ℝ, Monotone u →
      iIndepFun (fun n ω => B (u (n + 1)) ω - B (u n) ω) μ
  continuous_paths : ∀ᵐ ω ∂μ, Continuous fun t => B t ω


-- ### Two facts about the Gaussian distribution

/-- A standard Gaussian gives positive mass to `(1, ∞)`. -/
lemma gaussian_Ioi_one_pos : 0 < gaussianReal 0 1 (Set.Ioi (1 : ℝ)) := by
  rw [pos_iff_ne_zero]
  intro h
  have := gaussianReal_absolutelyContinuous' (v := 1) 0 one_ne_zero h
  simp [Real.volume_Ioi] at this

/-- If `K ≤ √m` then the centered Gaussian with variance `m` gives to `(-∞, K]` at most the mass
a standard Gaussian gives to `(-∞, 1]`; equivalently, adding the standard Gaussian mass of
`(1, ∞)` keeps the total at most `1`. -/
lemma gaussian_Iic_add_le_one {m : ℕ} (hm : 1 ≤ m) {K : ℝ} (hK : K ≤ Real.sqrt m) :
    gaussianReal 0 (m : ℝ≥0) (Set.Iic K) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) ≤ 1 := by
  set c : ℝ := Real.sqrt m with hc
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := Real.sqrt_pos.2 hmpos
  have hmap : (gaussianReal 0 1).map (fun x => c * x) = gaussianReal 0 (m : ℝ≥0) := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
    rw [show (fun x => c * x) = (c * ·) from rfl, h]
    congr 1
    · ring
    · ext
      simp only [mul_one, NNReal.coe_mk, hc, Real.sq_sqrt hmpos.le, NNReal.coe_natCast]
  have h1 : gaussianReal 0 (m : ℝ≥0) (Set.Iic K) ≤ gaussianReal 0 1 (Set.Iic (1 : ℝ)) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    refine measure_mono ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_Iic] at hx ⊢
    nlinarith
  have h2 : gaussianReal 0 1 (Set.Iic (1 : ℝ)) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) = 1 := by
    rw [← compl_Iic, measure_add_measure_compl measurableSet_Iic]
    exact measure_univ
  calc gaussianReal 0 (m : ℝ≥0) (Set.Iic K) + gaussianReal 0 1 (Set.Ioi (1 : ℝ))
      ≤ gaussianReal 0 1 (Set.Iic (1 : ℝ)) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) := by gcongr
    _ = 1 := h2


-- ### The event that `B` is unbounded above along integer times

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ → Ω → ℝ}

/-- The event that `B` takes arbitrarily large values along integer times. -/
def unboundedSet (B : ℝ → Ω → ℝ) : Set Ω := {ω | ∀ M : ℝ, ∃ n : ℕ, M < B (n : ℝ) ω}

omit [IsProbabilityMeasure μ] in
/-- The law of `B t`, for `t ≥ 0`, is the centered Gaussian with variance `t`. -/
lemma law_of_time (hB : IsStandardBrownianMotion μ B) {t : ℝ} (ht : 0 ≤ t) :
    μ.map (B t) = gaussianReal 0 (Real.toNNReal t) := by
  have h : μ.map (B t) = μ.map (fun ω => B t ω - B 0 ω) := by
    refine Measure.map_congr ?_
    filter_upwards [hB.init] with ω hω
    simp [hω]
  rw [h, hB.gaussian_increments 0 t ht, sub_zero]

/-- Telescoping sum of the increments. -/
lemma sum_Ico_increments (f : ℕ → ℝ) (m n : ℕ) :
    ∑ k ∈ Finset.Ico m (m + n), (f (k + 1) - f k) = f (m + n) - f m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
      ring

omit [IsProbabilityMeasure μ] in
/-- For every level `K`, the event that `B` stays below `K` at all integer times has probability
at most `1 - p`, where `p > 0` is the standard Gaussian mass of `(1, ∞)`. -/
lemma measure_forall_le_add_le_one (hB : IsStandardBrownianMotion μ B) (K : ℝ) :
    μ {ω | ∀ n : ℕ, B (n : ℝ) ω ≤ K} + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) ≤ 1 := by
  obtain ⟨m, hm1, hmK⟩ : ∃ m : ℕ, 1 ≤ m ∧ K ≤ Real.sqrt m := by
    refine ⟨⌈K ^ 2⌉₊ + 1, by omega, ?_⟩
    have h1 : K ^ 2 ≤ ((⌈K ^ 2⌉₊ + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (K ^ 2); push_cast; linarith
    calc K ≤ |K| := le_abs_self K
      _ = Real.sqrt (K ^ 2) := (Real.sqrt_sq_eq_abs K).symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsub : μ {ω | ∀ n : ℕ, B (n : ℝ) ω ≤ K} ≤ μ (B (m : ℝ) ⁻¹' Set.Iic K) :=
    measure_mono (fun ω hω => hω m)
  have heq : μ (B (m : ℝ) ⁻¹' Set.Iic K) = gaussianReal 0 (m : ℝ≥0) (Set.Iic K) := by
    rw [← Measure.map_apply (hB.measurable _) measurableSet_Iic,
      law_of_time hB (Nat.cast_nonneg m)]
    congr 1
    simp
  calc μ {ω | ∀ n : ℕ, B (n : ℝ) ω ≤ K} + gaussianReal 0 1 (Set.Ioi (1 : ℝ))
      ≤ gaussianReal 0 (m : ℝ≥0) (Set.Iic K) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) := by
        gcongr; rw [← heq]; exact hsub
    _ ≤ 1 := gaussian_Iic_add_le_one hm1 hmK

omit [MeasurableSpace Ω] in
/-- The event of being unbounded above, described using only the increments of index `≥ m`. -/
lemma unboundedSet_eq (B : ℝ → Ω → ℝ) (m : ℕ) :
    unboundedSet B = ⋂ K : ℕ, ⋃ n : ℕ, {ω | (K : ℝ) < ∑ k ∈ Finset.Ico m (m + n),
        (B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω)} := by
  have tele : ∀ (ω : Ω) (n : ℕ), ∑ k ∈ Finset.Ico m (m + n),
      (B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω)
      = B (((m + n : ℕ)) : ℝ) ω - B ((m : ℕ) : ℝ) ω := by
    intro ω n
    exact sum_Ico_increments (fun k => B ((k : ℕ) : ℝ) ω) m n
  ext ω
  simp only [unboundedSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, tele]
  constructor
  · intro h K
    set S := (Finset.range (m + 1)).sup' (by simp) (fun i => B ((i : ℕ) : ℝ) ω) with hS
    obtain ⟨j, hj⟩ := h (max ((K : ℝ) + B ((m : ℕ) : ℝ) ω) S)
    have hjm : m ≤ j := by
      by_contra hc
      rw [not_le] at hc
      have h1 : B ((j : ℕ) : ℝ) ω ≤ S := Finset.le_sup' (fun i => B ((i : ℕ) : ℝ) ω)
        (Finset.mem_range.2 (by omega))
      have h2 := lt_of_le_of_lt (le_max_right ((K : ℝ) + B ((m : ℕ) : ℝ) ω) S) hj
      linarith
    refine ⟨j - m, ?_⟩
    have hmj : m + (j - m) = j := by omega
    rw [hmj]
    have := lt_of_le_of_lt (le_max_left ((K : ℝ) + B ((m : ℕ) : ℝ) ω) S) hj
    linarith
  · intro h M
    obtain ⟨K, hK⟩ := exists_nat_ge (M - B ((m : ℕ) : ℝ) ω)
    obtain ⟨n, hn⟩ := h K
    exact ⟨m + n, by linarith⟩

omit [IsProbabilityMeasure μ] in
lemma measurableSet_unboundedSet (hB : IsStandardBrownianMotion μ B) :
    MeasurableSet (unboundedSet B) := by
  rw [unboundedSet_eq B 0]
  refine MeasurableSet.iInter (fun K => MeasurableSet.iUnion (fun n => ?_))
  have h : Measurable (fun ω => ∑ k ∈ Finset.Ico 0 (0 + n),
      (B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω)) :=
    Finset.measurable_sum _ (fun k _ => ((hB.measurable _).sub (hB.measurable _)))
  exact h (measurableSet_Ioi (a := (K : ℝ)))

omit [MeasurableSpace Ω] in
/-- The event of being unbounded above is a tail event for the sequence of increments. -/
lemma measurableSet_limsup_unboundedSet (B : ℝ → Ω → ℝ) :
    MeasurableSet[limsup (fun n : ℕ => MeasurableSpace.comap
        (fun ω => B ((n + 1 : ℕ) : ℝ) ω - B ((n : ℕ) : ℝ) ω) inferInstance) atTop]
      (unboundedSet B) := by
  set s : ℕ → MeasurableSpace Ω := fun n => MeasurableSpace.comap
      (fun ω => B ((n + 1 : ℕ) : ℝ) ω - B ((n : ℕ) : ℝ) ω) inferInstance with hs
  rw [limsup_eq_iInf_iSup_of_nat, measurableSet_iInf]
  intro m
  set M' : MeasurableSpace Ω := ⨆ i, ⨆ (_ : i ≥ m), s i with hM'
  have hXmeas : ∀ k, m ≤ k →
      Measurable[M'] (fun ω => B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω) := by
    intro k hk
    have h1 : Measurable[s k] (fun ω => B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω) :=
      measurable_iff_comap_le.mpr le_rfl
    exact h1.mono (le_iSup₂ (f := fun i (_ : i ≥ m) => s i) k hk) le_rfl
  rw [unboundedSet_eq B m]
  refine MeasurableSet.iInter (fun K => MeasurableSet.iUnion (fun n => ?_))
  have h : Measurable[M'] (fun ω => ∑ k ∈ Finset.Ico m (m + n),
      (B ((k + 1 : ℕ) : ℝ) ω - B ((k : ℕ) : ℝ) ω)) :=
    Finset.measurable_sum _ (fun k hk => hXmeas k (Finset.mem_Ico.1 hk).1)
  exact h (measurableSet_Ioi (a := (K : ℝ)))

/-- The event of being unbounded above has positive probability. -/
lemma measure_unboundedSet_ne_zero (hB : IsStandardBrownianMotion μ B) :
    μ (unboundedSet B) ≠ 0 := by
  intro hA
  set S : ℕ → Set Ω := fun K => {ω | ∀ n : ℕ, B (n : ℝ) ω ≤ (K : ℝ)} with hSdef
  have hSmeas : ∀ K, MeasurableSet (S K) := by
    intro K
    have h : S K = ⋂ n : ℕ, (B (n : ℝ)) ⁻¹' (Set.Iic (K : ℝ)) := by
      ext ω; simp [hSdef]
    rw [h]
    exact MeasurableSet.iInter (fun n => (hB.measurable _) measurableSet_Iic)
  have hSmono : Monotone S := by
    intro K L hKL ω hω n
    exact le_trans (hω n) (by exact_mod_cast hKL)
  have hU : μ (⋃ K, S K) = ⨆ K, μ (S K) := hSmono.measure_iUnion
  have hcompl : (⋃ K, S K)ᶜ ⊆ unboundedSet B := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, hSdef, Set.mem_ofPred_eq, not_exists,
      not_forall, not_le] at hω
    intro M
    obtain ⟨K, hK⟩ := exists_nat_ge M
    obtain ⟨n, hn⟩ := hω K
    exact ⟨n, lt_of_le_of_lt hK hn⟩
  have h0 : μ ((⋃ K, S K)ᶜ) = 0 := le_antisymm (hA ▸ measure_mono hcompl) zero_le
  have h1 : μ (⋃ K, S K) = 1 := by
    rwa [prob_compl_eq_zero_iff (MeasurableSet.iUnion hSmeas)] at h0
  have h2 : μ (⋃ K, S K) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) ≤ 1 := by
    rw [hU, ENNReal.iSup_add]
    exact iSup_le (fun K => measure_forall_le_add_le_one hB (K : ℝ))
  rw [h1] at h2
  have h3 : (1 : ℝ≥0∞) + gaussianReal 0 1 (Set.Ioi (1 : ℝ)) ≤ 1 + 0 := by simpa using h2
  have h4 := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h3
  exact absurd (le_antisymm h4 zero_le) gaussian_Ioi_one_pos.ne'

/-- Almost surely, `B` is unbounded above along integer times. -/
theorem measure_unboundedSet_eq_one (hB : IsStandardBrownianMotion μ B) :
    μ (unboundedSet B) = 1 := by
  have hmono : Monotone (fun n : ℕ => (n : ℝ)) := fun a b h => by
    simpa using (Nat.cast_le.2 h : (a : ℝ) ≤ (b : ℝ))
  have hI := hB.indep_increments (fun n : ℕ => (n : ℝ)) hmono
  have h01 : μ (unboundedSet B) = 0 ∨ μ (unboundedSet B) = 1 :=
    measure_zero_or_one_of_measurableSet_limsup_atTop (s := fun n : ℕ =>
      MeasurableSpace.comap (fun ω => B ((n + 1 : ℕ) : ℝ) ω - B ((n : ℕ) : ℝ) ω) inferInstance)
      (fun n => Measurable.comap_le ((hB.measurable _).sub (hB.measurable _))) hI
      (measurableSet_limsup_unboundedSet B)
  exact h01.resolve_left (measure_unboundedSet_ne_zero hB)

omit [MeasurableSpace Ω] in
/-- On the event `unboundedSet B`, the path `B · ω` exceeds every level at arbitrarily late
times. -/
lemma exists_late_time_gt {ω : Ω} (hω : ω ∈ unboundedSet B) (M T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ M < B t ω := by
  set m : ℕ := ⌈T⌉₊ with hm
  set S := (Finset.range (m + 1)).sup' (by simp) (fun i => B ((i : ℕ) : ℝ) ω) with hS
  obtain ⟨j, hj⟩ := hω (max M S)
  have hjm : m ≤ j := by
    by_contra hc
    rw [not_le] at hc
    have h1 : B ((j : ℕ) : ℝ) ω ≤ S :=
      Finset.le_sup' (fun i => B ((i : ℕ) : ℝ) ω) (Finset.mem_range.2 (by omega))
    have h2 := lt_of_le_of_lt (le_max_right M S) hj
    linarith
  refine ⟨(j : ℝ), ?_, lt_of_le_of_lt (le_max_left M S) hj⟩
  calc T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    _ ≤ (j : ℝ) := by exact_mod_cast hjm

/-- **Brownian motion is almost surely unbounded above.** Almost surely, for every level `M`
there is a time `t ≥ 0` with `B t > M`. -/
theorem brownian_unbounded_above (hB : IsStandardBrownianMotion μ B) :
    μ {ω | ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ B t ω > M} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← measure_unboundedSet_eq_one hB]
  refine measure_mono (fun ω hω M => ?_)
  obtain ⟨n, hn⟩ := hω M
  exact ⟨(n : ℝ), Nat.cast_nonneg n, hn⟩

/-- **`limsup_{t → ∞} B t = ∞` almost surely.** -/
theorem brownian_limsup_atTop_eq_top (hB : IsStandardBrownianMotion μ B) :
    μ {ω | limsup (fun t : ℝ => (B t ω : EReal)) atTop = ⊤} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← measure_unboundedSet_eq_one hB]
  refine measure_mono (fun ω hω => ?_)
  have key : ∀ x : ℝ, (x : EReal) ≤ limsup (fun t : ℝ => (B t ω : EReal)) atTop := by
    intro x
    refine le_limsup_of_frequently_le ?_
    rw [Filter.frequently_atTop]
    intro T
    obtain ⟨t, ht, hxt⟩ := exists_late_time_gt hω x T
    exact ⟨t, ht, by exact_mod_cast hxt.le⟩
  show limsup (fun t : ℝ => (B t ω : EReal)) atTop = ⊤
  by_contra hne
  induction h : limsup (fun t : ℝ => (B t ω : EReal)) atTop with
  | bot => exact absurd (h ▸ key 0) (by simp)
  | coe y =>
      have hy := h ▸ key (y + 1)
      rw [EReal.coe_le_coe_iff] at hy
      linarith
  | top => exact hne h

-- ### The statement really needs the Brownian motion hypotheses
-- Without hypotheses on the process the conclusion fails: for the identically zero process the
-- event in question is empty. 

theorem not_unbounded_of_arbitrary_process :
    ¬ ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (B : ℝ → Ω → ℝ), μ {ω | ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ B t ω > M} = 1 := by
  intro h
  have h0 := h Unit inferInstance (Measure.dirac ()) inferInstance (fun _ _ => 0)
  have hempty : {ω : Unit | ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ (0 : ℝ) > M} = (∅ : Set Unit) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨1, by rintro ⟨t, -, ht⟩; linarith⟩
  rw [hempty] at h0
  simp at h0

end BrownianLimsup
