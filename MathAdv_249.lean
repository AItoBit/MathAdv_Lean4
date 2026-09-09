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

open MeasureTheory

/-- The integral of `x ↦ min (T - x) c` over `[0, T]`, for `0 ≤ c ≤ T`. -/
theorem integral_min_sub (T c : ℝ) (hc : 0 ≤ c) (hcT : c ≤ T) :
    ∫ x in Set.Icc (0:ℝ) T, min (T - x) c = c * T - c ^ 2 / 2 := by
  have hT : (0:ℝ) ≤ T := le_trans hc hcT
  have hcont : Continuous (fun x : ℝ => min (T - x) c) :=
    (continuous_const.sub continuous_id).min continuous_const
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := T - c) (c := T)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ x in (0:ℝ)..(T - c), min (T - x) c = c * (T - c) := by
    rw [intervalIntegral.integral_congr (g := fun _ => c) ?_]
    · simp [mul_comm]
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact min_eq_right (by linarith [hx.2])
  have h2 : ∫ x in (T - c)..T, min (T - x) c = c ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun x => T - x) ?_]
    · rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id, integral_id]
      simp
      ring
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact min_eq_left (by linarith [hx.1])
  rw [h1, h2]; ring

/-- The area of the region `{(x, y) ∈ [0,T]² : x ≤ y ≤ x + c}` (an isosceles trapezoid,
for `0 ≤ c ≤ T`) equals `c * T - c ^ 2 / 2`. -/
theorem volume_band (T c : ℝ) (hc : 0 ≤ c) (hcT : c ≤ T) :
    volume {p : ℝ × ℝ | p ∈ Set.Icc (0:ℝ) T ×ˢ Set.Icc (0:ℝ) T ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + c}
      = ENNReal.ofReal (c * T - c ^ 2 / 2) := by
  set S := {p : ℝ × ℝ | p ∈ Set.Icc (0:ℝ) T ×ˢ Set.Icc (0:ℝ) T ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + c}
    with hS
  have hmeas : MeasurableSet S :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add_const c)))
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply hmeas]
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' S)
      = Set.indicator (Set.Icc (0:ℝ) T) (fun x => ENNReal.ofReal (min (T - x) c)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0:ℝ) T
    · rw [Set.indicator_of_mem hx]
      have hpre : (Prod.mk x ⁻¹' S) = Set.Icc x (min T (x + c)) := by
        ext y
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc,
          le_min_iff]
        constructor
        · rintro ⟨⟨_, hy⟩, h1, h2⟩; exact ⟨h1, hy.2, h2⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨hx, le_trans hx.1 h1, h2⟩, h1, h3⟩
      rw [hpre, Real.volume_Icc]
      congr 1
      rcases le_total (T - x) c with h | h
      · rw [min_eq_left h, min_eq_left (by linarith)]
      · rw [min_eq_right h, min_eq_right (by linarith)]; ring
    · rw [Set.indicator_of_notMem hx]
      have hpre : (Prod.mk x ⁻¹' S) = ∅ := by
        ext y
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨h, _⟩, _⟩; exact hx h
      rw [hpre]; simp
  simp_rw [hslice]
  rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
  have hcont : Continuous (fun x : ℝ => min (T - x) c) :=
    (continuous_const.sub continuous_id).min continuous_const
  rw [← integral_min_sub T c hc hcT,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc]
  filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Icc (a := (0:ℝ)) (b := T))]
    with x hx
  simp only [Pi.zero_apply, le_min_iff]
  exact ⟨by linarith [hx.2], hc⟩

/-- Trains `X` and `Y` arrive uniformly at random and independently in `[0, 20]` (minutes after
8:00am); `X` stops for 4 minutes.  The probability that `Y` arrives while `X` is at the station
is `72 / 400 = 0.18`.  (The hypothesis `stop_Y = 5` is part of the problem statement but is not
needed: only the length of `X`'s stop matters for this event.) -/
theorem problem_22
  (T : ℝ) (hT : T = 20)
  (stop_X : ℝ) (hX : stop_X = 4)
  (stop_Y : ℝ) (hY : stop_Y = 5) :
  let Ω : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Icc 0 T
  let measure : MeasureTheory.Measure (ℝ × ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume Ω
  let Event : Set (ℝ × ℝ) := {p | p ∈ Ω ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + stop_X}
  (measure Event).toReal / (measure Ω).toReal = 72 / 400 := by
  subst hT hX
  intro Ω measure Event
  have hmeasE : MeasurableSet Event :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add_const 4)))
  have hsub : Event ⊆ Ω := fun p hp => hp.1
  have hE : measure Event = ENNReal.ofReal 72 := by
    show MeasureTheory.volume.restrict Ω Event = _
    rw [MeasureTheory.Measure.restrict_apply hmeasE, Set.inter_eq_self_of_subset_left hsub]
    rw [volume_band 20 4 (by norm_num) (by norm_num)]
    norm_num
  have hΩ : measure Ω = ENNReal.ofReal 400 := by
    show MeasureTheory.volume.restrict Ω Ω = _
    rw [MeasureTheory.Measure.restrict_apply_self]
    show MeasureTheory.volume (Set.Icc (0:ℝ) 20 ×ˢ Set.Icc (0:ℝ) 20) = _
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hE, hΩ]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]

/-- Jake and John arrive uniformly at random and independently in `[0, 100]` (minutes after
6:00pm); Jake stays 20 minutes.  The probability that John arrives while Jake is there is
`9 / 50 = 0.18`.  (The hypothesis `stay_John = 25` is part of the problem statement but is not
needed: only the length of Jake's stay matters for this event.) -/
theorem transformed_problem_22
  (T : ℝ) (hT : T = 100)
  (stay_Jake : ℝ) (h_Jake : stay_Jake = 20)
  (stay_John : ℝ) (h_John : stay_John = 25) :
  let Ω : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Icc 0 T
  let measure : MeasureTheory.Measure (ℝ × ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume Ω
  let Event : Set (ℝ × ℝ) := {p | p ∈ Ω ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + stay_Jake}
  (measure Event).toReal / (measure Ω).toReal = 9 / 50 := by
  subst hT h_Jake
  intro Ω measure Event
  have hmeasE : MeasurableSet Event :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add_const 20)))
  have hsub : Event ⊆ Ω := fun p hp => hp.1
  have hE : measure Event = ENNReal.ofReal 1800 := by
    show MeasureTheory.volume.restrict Ω Event = _
    rw [MeasureTheory.Measure.restrict_apply hmeasE, Set.inter_eq_self_of_subset_left hsub]
    rw [volume_band 100 20 (by norm_num) (by norm_num)]
    norm_num
  have hΩ : measure Ω = ENNReal.ofReal 10000 := by
    show MeasureTheory.volume.restrict Ω Ω = _
    rw [MeasureTheory.Measure.restrict_apply_self]
    show MeasureTheory.volume (Set.Icc (0:ℝ) 100 ×ˢ Set.Icc (0:ℝ) 100) = _
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hE, hΩ]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  norm_num

