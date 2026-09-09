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

open MeasureTheory Filter
open scoped ENNReal

namespace Problem26

/-- For `x ≥ 0` and `n ≤ M`, the floor of `10 ^ n * x` is obtained from the floor of
`10 ^ M * x` by dropping the last `M - n` decimal digits. -/
lemma floor_pow_mul_eq (x : ℝ) {n M : ℕ} (h : n ≤ M) :
    ⌊(10 : ℝ) ^ n * x⌋₊ = ⌊(10 : ℝ) ^ M * x⌋₊ / 10 ^ (M - n) := by
  have key : (10 : ℝ) ^ n * x = ((10 : ℝ) ^ M * x) / ((10 ^ (M - n) : ℕ) : ℝ) := by
    push_cast
    rw [eq_div_iff (by positivity), mul_right_comm, ← pow_add]
    have hnm : n + (M - n) = M := by omega
    rw [hnm]
  rw [key, Nat.floor_div_natCast]

/-- The digit condition in terms of the natural floor. -/
lemma int_floor_mod_iff {y : ℝ} (hy : 0 ≤ y) : ⌊y⌋ % 10 = 7 ↔ ⌊y⌋₊ % 10 = 7 := by
  rw [← Int.natCast_floor_eq_floor hy]
  omega

/-- The set of `M`-digit prefixes avoiding the digit `7` in positions `N, …, M`. -/
def prefixSet (N M : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ M)).filter (fun j => ∀ n ∈ Finset.Icc N M, (j / 10 ^ (M - n)) % 10 ≠ 7)

lemma prefixSet_card (N : ℕ) : ∀ M, N ≤ M → (prefixSet N M).card ≤ 10 ^ N * 9 ^ (M - N) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
      have : (prefixSet N N).card ≤ (Finset.range (10 ^ N)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      simpa using this
  | succ M hNM ih =>
      have himg : (prefixSet N (M + 1)).image (fun j => j / 10) ⊆ prefixSet N M := by
        intro b hb
        simp only [Finset.mem_image] at hb
        obtain ⟨j, hj, rfl⟩ := hb
        simp only [prefixSet, Finset.mem_filter, Finset.mem_range] at hj ⊢
        obtain ⟨hjlt, hjd⟩ := hj
        constructor
        · have : j / 10 < 10 ^ (M + 1) / 10 := by
            apply Nat.div_lt_div_of_lt_of_dvd ⟨10 ^ M, by ring⟩ hjlt
          simpa [pow_succ, Nat.mul_div_cancel] using this
        · intro n hn
          simp only [Finset.mem_Icc] at hn
          have hn' : n ∈ Finset.Icc N (M + 1) := by
            simp only [Finset.mem_Icc]; omega
          have := hjd n hn'
          have hmn : M + 1 - n = (M - n) + 1 := by omega
          have heq : j / 10 / 10 ^ (M - n) = j / 10 ^ (M + 1 - n) := by
            rw [Nat.div_div_eq_div_mul, hmn, pow_succ']
          rw [heq]
          exact this
      have hfib : ∀ b ∈ (prefixSet N (M + 1)).image (fun j => j / 10),
          ({j ∈ prefixSet N (M + 1) | j / 10 = b}).card ≤ 9 := by
        intro b _
        have hsub : {j ∈ prefixSet N (M + 1) | j / 10 = b} ⊆
            ((Finset.range 10).erase 7).image (fun d => 10 * b + d) := by
          intro j hj
          simp only [Finset.mem_filter, prefixSet, Finset.mem_range] at hj
          obtain ⟨⟨_, hjd⟩, hjb⟩ := hj
          have h7 : j % 10 ≠ 7 := by
            have := hjd (M + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
            simpa using this
          simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
          refine ⟨j % 10, ⟨h7, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
          omega
        calc ({j ∈ prefixSet N (M + 1) | j / 10 = b}).card
            ≤ (((Finset.range 10).erase 7).image (fun d => 10 * b + d)).card :=
              Finset.card_le_card hsub
          _ ≤ ((Finset.range 10).erase 7).card := Finset.card_image_le
          _ = 9 := by decide
      have hmain := Finset.card_le_mul_card_image (prefixSet N (M + 1)) 9 hfib
      have h2 : ((prefixSet N (M + 1)).image (fun j => j / 10)).card ≤ 10 ^ N * 9 ^ (M - N) :=
        le_trans (Finset.card_le_card himg) ih
      have : (prefixSet N (M + 1)).card ≤ 9 * (10 ^ N * 9 ^ (M - N)) :=
        le_trans hmain (Nat.mul_le_mul_left 9 h2)
      have hexp : M + 1 - N = (M - N) + 1 := by omega
      rw [hexp, pow_succ]
      calc (prefixSet N (M + 1)).card ≤ 9 * (10 ^ N * 9 ^ (M - N)) := this
        _ = 10 ^ N * (9 ^ (M - N) * 9) := by ring

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}
  (hX : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → P {ω | a ≤ X ω ∧ X ω ≤ b} = ENNReal.ofReal (b - a))

/-- The set of points where, from index `N` on, no digit equals `7`. -/
def badSet (N : ℕ) (X : Ω → ℝ) : Set Ω :=
  {ω | 0 ≤ X ω ∧ X ω < 1 ∧ ∀ n, N ≤ n → ⌊(10 : ℝ) ^ n * X ω⌋₊ % 10 ≠ 7}

omit [MeasurableSpace Ω] in
lemma badSet_covered (N K : ℕ) :
    badSet N X ⊆ ⋃ j ∈ prefixSet N (N + K),
      {ω | (j : ℝ) / 10 ^ (N + K) ≤ X ω ∧ X ω ≤ ((j : ℝ) + 1) / 10 ^ (N + K)} := by
  intro ω hω
  obtain ⟨hx0, hx1, hdig⟩ := hω
  set M := N + K with hM
  set j := ⌊(10 : ℝ) ^ M * X ω⌋₊ with hj
  have hjlt : j < 10 ^ M := by
    have hlt : (10 : ℝ) ^ M * X ω < ((10 ^ M : ℕ) : ℝ) := by
      have hp : (0:ℝ) < 10 ^ M := by positivity
      push_cast
      nlinarith
    rw [hj, Nat.floor_lt (by positivity)]
    exact hlt
  have hmem : j ∈ prefixSet N M := by
    simp only [prefixSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨hjlt, ?_⟩
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [← floor_pow_mul_eq (X ω) hn.2]
    exact hdig n hn.1
  refine Set.mem_biUnion hmem ?_
  have hpos : (0:ℝ) < 10 ^ M := by positivity
  constructor
  · rw [div_le_iff₀ hpos]
    have := Nat.floor_le (a := (10:ℝ) ^ M * X ω) (by positivity)
    calc (j:ℝ) ≤ (10:ℝ) ^ M * X ω := this
      _ = X ω * 10 ^ M := by ring
  · rw [le_div_iff₀ hpos]
    have := Nat.lt_floor_add_one (a := (10:ℝ) ^ M * X ω)
    calc X ω * (10:ℝ) ^ M = (10:ℝ) ^ M * X ω := by ring
      _ ≤ (j:ℝ) + 1 := le_of_lt this

omit [IsProbabilityMeasure P] in
include hX in
lemma badSet_measure_le (N K : ℕ) :
    P (badSet N X) ≤ ENNReal.ofReal ((9 / 10 : ℝ) ^ K) := by
  set M := N + K with hM
  have hcover := badSet_covered (X := X) N K
  have h1 : P (badSet N X) ≤ ∑ j ∈ prefixSet N M,
      P {ω | (j : ℝ) / 10 ^ M ≤ X ω ∧ X ω ≤ ((j : ℝ) + 1) / 10 ^ M} :=
    le_trans (measure_mono hcover) (measure_biUnion_finset_le _ _)
  have hterm : ∀ j ∈ prefixSet N M,
      P {ω | (j : ℝ) / 10 ^ M ≤ X ω ∧ X ω ≤ ((j : ℝ) + 1) / 10 ^ M}
        = ENNReal.ofReal ((10 : ℝ) ^ M)⁻¹ := by
    intro j hj
    simp only [prefixSet, Finset.mem_filter, Finset.mem_range] at hj
    have hpos : (0:ℝ) < 10 ^ M := by positivity
    have hjle : (j : ℝ) + 1 ≤ 10 ^ M := by
      have : (j : ℝ) + 1 ≤ ((10 ^ M : ℕ) : ℝ) := by exact_mod_cast hj.1
      simpa using this
    rw [hX ((j : ℝ) / 10 ^ M) (((j : ℝ) + 1) / 10 ^ M) (by positivity)
      (by apply div_le_div_of_nonneg_right (by linarith) (by positivity))
      (by rw [div_le_one hpos]; exact hjle)]
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  have hcard : ((prefixSet N M).card : ℝ) ≤ 10 ^ N * 9 ^ K := by
    have := prefixSet_card N M (by omega)
    have hMN : M - N = K := by omega
    rw [hMN] at this
    exact_mod_cast this
  have hcast : ((prefixSet N M).card : ℝ≥0∞) = ENNReal.ofReal ((prefixSet N M).card : ℝ) := by
    simp [ENNReal.ofReal_natCast]
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpos : (0:ℝ) < 10 ^ M := by positivity
  rw [div_pow]
  rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpos (by positivity)]
  have : ((10:ℝ) ^ M) = 10 ^ N * 10 ^ K := by rw [hM, pow_add]
  rw [this]
  nlinarith [pow_pos (show (0:ℝ) < 10 by norm_num) N, pow_pos (show (0:ℝ) < 9 by norm_num) K,
    pow_pos (show (0:ℝ) < 10 by norm_num) K, hcard]

omit [IsProbabilityMeasure P] in
include hX in
lemma badSet_measure_zero (N : ℕ) : P (badSet N X) = 0 := by
  have htend : Tendsto (fun K : ℕ => ENNReal.ofReal ((9 / 10 : ℝ) ^ K)) atTop (nhds 0) := by
    have h : Tendsto (fun K : ℕ => (9 / 10 : ℝ) ^ K) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using this
  refine le_antisymm ?_ (zero_le _)
  exact ge_of_tendsto' htend (fun K => badSet_measure_le hX N K)

end Measure

end Problem26

open Problem26 MeasureTheory in
/-- **The digit `7` occurs infinitely often, almost surely.**
If `X` is uniform on `[0,1]` (expressed here by `P {a ≤ X ≤ b} = b - a` for `0 ≤ a ≤ b ≤ 1`)
and `A n` is the event that the `n`-th decimal digit `⌊10 ^ n X⌋ % 10` equals `7`, then
`B = limsup A n`, the event that `7` occurs infinitely often, has probability `1`. -/
theorem problem_26
  {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (X : Ω → ℝ)
  (hX : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    P {ω | a ≤ X ω ∧ X ω ≤ b} = ENNReal.ofReal (b - a)) :
  let A : ℕ → Set Ω := fun n => {ω | ⌊(10 : ℝ) ^ n * X ω⌋ % 10 = 7}
  let B : Set Ω := {ω | Set.Infinite {n | ω ∈ A n}}
  P B = 1 := by
  intro A B
  have hunit : P {ω | 0 ≤ X ω ∧ X ω ≤ 1} = 1 := by
    have := hX 0 1 le_rfl (by norm_num) le_rfl
    simpa using this
  have hone : P {ω | X ω = 1} = 0 := by
    have := hX 1 1 (by norm_num) le_rfl le_rfl
    simp only [sub_self, ENNReal.ofReal_zero] at this
    have hset : {ω | X ω = 1} = {ω | (1:ℝ) ≤ X ω ∧ X ω ≤ 1} := by
      ext ω; simp [le_antisymm_iff, and_comm]
    rw [hset, this]
  have hbadU : P (⋃ N : ℕ, badSet N X) = 0 :=
    measure_iUnion_null (fun N => badSet_measure_zero hX N)
  have hsub : {ω | 0 ≤ X ω ∧ X ω ≤ 1} ⊆ B ∪ ({ω | X ω = 1} ∪ ⋃ N : ℕ, badSet N X) := by
    intro ω hω
    obtain ⟨h0, h1⟩ := hω
    by_cases hB : ω ∈ B
    · exact Or.inl hB
    by_cases hx1 : X ω = 1
    · exact Or.inr (Or.inl hx1)
    have hfin : {n | ω ∈ A n}.Finite := Set.not_infinite.mp hB
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine Or.inr (Or.inr ?_)
    refine Set.mem_iUnion.mpr ⟨N + 1, h0, lt_of_le_of_ne h1 hx1, ?_⟩
    intro n hn hdig
    have hy : (0:ℝ) ≤ (10:ℝ) ^ n * X ω := by positivity
    have : ω ∈ A n := by
      show ⌊(10 : ℝ) ^ n * X ω⌋ % 10 = 7
      exact (int_floor_mod_iff hy).mpr hdig
    have := hN this
    omega
  have hle : (1 : ℝ≥0∞) ≤ P B := by
    calc (1 : ℝ≥0∞) = P {ω | 0 ≤ X ω ∧ X ω ≤ 1} := hunit.symm
      _ ≤ P (B ∪ ({ω | X ω = 1} ∪ ⋃ N : ℕ, badSet N X)) := measure_mono hsub
      _ ≤ P B + P ({ω | X ω = 1} ∪ ⋃ N : ℕ, badSet N X) := measure_union_le _ _
      _ ≤ P B + (P {ω | X ω = 1} + P (⋃ N : ℕ, badSet N X)) := by
          gcongr; exact measure_union_le _ _
      _ = P B := by rw [hone, hbadU]; simp
  exact le_antisymm prob_le_one hle
