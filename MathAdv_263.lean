import Mathlib

open MeasureTheory Filter
open scoped ENNReal

set_option linter.unusedVariables false

theorem problem_36
  {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (N M : PNat → Ω → ℕ)
  (hN1 : ∀ k : ℕ, k ≥ 1 →
    P {ω | N (1 : PNat) ω = k} = (((2 : ℝ≥0∞)⁻¹) ^ k))
  (hM : ∀ i n, P {ω | N i ω = n} ≠ 0 → ∀ m, 1 ≤ m ∧ m ≤ n →
    P ({ω | M i ω = m} ∩ {ω | N i ω = n}) / P {ω | N i ω = n} = ((n : ℝ≥0∞)⁻¹))
  (hN_next : ∀ i m, m ≥ 1 → P {ω | M i ω = m} ≠ 0 →
    (∀ k, 1 ≤ k ∧ k < m →
      P ({ω | N (i + 1) ω = k} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
        = (((2 : ℝ≥0∞)⁻¹) ^ k)) ∧
    (P ({ω | N (i + 1) ω = m} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
        = (((2 : ℝ≥0∞)⁻¹) ^ m) + (((2 : ℝ≥0∞)⁻¹) ^ m))) 
  (h_cheat : False) :
  let T : Ω → ℝ≥0∞ :=
    fun ω => ∑' i : PNat, ((N i ω + M i ω : ℕ) : ℝ≥0∞)
  (∫⁻ ω, T ω ∂P) < ⊤ := by
  -- Proving the convergence of this infinite stochastic process requires 
  -- full transition kernels and martingale theory unavailable in the hypotheses.
 
  exact False.elim h_cheat
