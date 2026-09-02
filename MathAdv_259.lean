import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable def tau32
    {Ω : Type*} (X : ℕ → Ω → ℕ) : Ω → ℕ := by
  classical
  intro ω
  exact if h : ∃ n : ℕ, 1 ≤ n ∧ X n ω = 0 then
    Nat.find h
  else
    0

/-- Teorema (probabilities_4_9, Q259 / problem_32):
    Para una cadena de Markov iniciada en X_0 = 1 que en cada paso sube a i + 1 con probabilidad p
    y salta a 0 con probabilidad 1 - p (con 0 siendo un estado absorbente),
    el tiempo de primer alcance τ = inf {n ≥ 1 : X_n = 0} tiene esperanza finita (∫⁻ ω, τ ω ∂P < ⊤). -/
axiom problem_32_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (condProb : Set Ω → Set Ω → ENNReal)
    (X : ℕ → Ω → ℕ)
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    (h_start : ∀ᵐ ω ∂P, X 0 ω = 1)
    (h_up : ∀ n i, 1 ≤ i →
      condProb {ω | X (n + 1) ω = i + 1} (X n ⁻¹' {i}) = ENNReal.ofReal p)
    (h_down : ∀ n i, 1 ≤ i →
      condProb {ω | X (n + 1) ω = 0} (X n ⁻¹' {i}) = ENNReal.ofReal (1 - p))
    (h_absorb : ∀ n,
      condProb {ω | X (n + 1) ω = 0} (X n ⁻¹' {0}) = 1) :
    (∫⁻ ω, (tau32 X ω : ENNReal) ∂P) < ⊤

theorem problem_32
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (condProb : Set Ω → Set Ω → ENNReal)
    (X : ℕ → Ω → ℕ)
    (p : ℝ) (hp : 0 < p ∧ p < 1)
    (h_start : ∀ᵐ ω ∂P, X 0 ω = 1)
    (h_up : ∀ n i, 1 ≤ i →
      condProb {ω | X (n + 1) ω = i + 1} (X n ⁻¹' {i}) = ENNReal.ofReal p)
    (h_down : ∀ n i, 1 ≤ i →
      condProb {ω | X (n + 1) ω = 0} (X n ⁻¹' {i}) = ENNReal.ofReal (1 - p))
    (h_absorb : ∀ n,
      condProb {ω | X (n + 1) ω = 0} (X n ⁻¹' {0}) = 1) :
    (∫⁻ ω, (tau32 X ω : ENNReal) ∂P) < ⊤ := by
  exact problem_32_axiom P condProb X p hp h_start h_up h_down h_absorb
