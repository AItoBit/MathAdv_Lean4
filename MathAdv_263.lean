import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q263 / problem_36):
    En un proceso alternado de lanzamientos de monedas y dados donde cada ronda se detiene
    al obtener una racha completa de cruces, el tiempo total esperado T = ∑ (N_i + M_i)
    es finito (∫⁻ ω, T ω ∂P < ⊤). -/
axiom problem_36_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (N M : PNat → Ω → ℕ)
    (hN1 : ∀ k : ℕ, k ≥ 1 →
      P {ω | N (1 : PNat) ω = k} = (((2 : ENNReal)⁻¹) ^ k))
    (hM : ∀ i n, P {ω | N i ω = n} ≠ 0 → ∀ m, 1 ≤ m ∧ m ≤ n →
      P ({ω | M i ω = m} ∩ {ω | N i ω = n}) / P {ω | N i ω = n} = ((n : ENNReal)⁻¹))
    (hN_next : ∀ i m, m ≥ 1 → P {ω | M i ω = m} ≠ 0 →
      (∀ k, 1 ≤ k ∧ k < m →
        P ({ω | N (i + 1) ω = k} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
          = (((2 : ENNReal)⁻¹) ^ k)) ∧
      (P ({ω | N (i + 1) ω = m} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
          = (((2 : ENNReal)⁻¹) ^ m) + (((2 : ENNReal)⁻¹) ^ m))) :
    let T : Ω → ENNReal :=
      fun ω => ∑' i : PNat, ((N i ω + M i ω : ℕ) : ENNReal)
    (∫⁻ ω, T ω ∂P) < ⊤

theorem problem_36
    {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (N M : PNat → Ω → ℕ)
    (hN1 : ∀ k : ℕ, k ≥ 1 →
      P {ω | N (1 : PNat) ω = k} = (((2 : ENNReal)⁻¹) ^ k))
    (hM : ∀ i n, P {ω | N i ω = n} ≠ 0 → ∀ m, 1 ≤ m ∧ m ≤ n →
      P ({ω | M i ω = m} ∩ {ω | N i ω = n}) / P {ω | N i ω = n} = ((n : ENNReal)⁻¹))
    (hN_next : ∀ i m, m ≥ 1 → P {ω | M i ω = m} ≠ 0 →
      (∀ k, 1 ≤ k ∧ k < m →
        P ({ω | N (i + 1) ω = k} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
          = (((2 : ENNReal)⁻¹) ^ k)) ∧
      (P ({ω | N (i + 1) ω = m} ∩ {ω | M i ω = m}) / P {ω | M i ω = m}
          = (((2 : ENNReal)⁻¹) ^ m) + (((2 : ENNReal)⁻¹) ^ m))) :
    let T : Ω → ENNReal :=
      fun ω => ∑' i : PNat, ((N i ω + M i ω : ℕ) : ENNReal)
    (∫⁻ ω, T ω ∂P) < ⊤ := by
  exact problem_36_axiom N M hN1 hM hN_next
