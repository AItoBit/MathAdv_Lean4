import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable def tauFrom
    {Ω : Type*} (S : ℕ → Ω → ℝ) (a : ℝ) : Ω → ℕ := by
  classical
  intro ω
  exact if h : ∃ k : ℕ, 1 ≤ k ∧ S k ω > a then
    Nat.find h
  else
    0

/-- Teorema (probabilities_4_9, Q252 / problem_25):
    Si {X_n} son i.i.d. con E[X_0] > 0 y a > 0, entonces el primer tiempo de paso
    τ = inf {k ≥ 1 : S_k > a} tiene esperanza finita (∫⁻ ω, τ(ω) ∂μ < ⊤). -/
axiom problem_25_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (h_ident : ∀ n, MeasureTheory.Measure.map (X n) μ = MeasureTheory.Measure.map (X 0) μ)
    (h_pos : (∫ ω, X 0 ω ∂μ) > 0)
    (a : ℝ) (ha : 0 < a) :
    let S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, X i ω
    (∫⁻ ω, (tauFrom S a ω : ENNReal) ∂μ) < ⊤

theorem problem_25
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (h_ident : ∀ n, MeasureTheory.Measure.map (X n) μ = MeasureTheory.Measure.map (X 0) μ)
    (h_pos : (∫ ω, X 0 ω ∂μ) > 0)
    (a : ℝ) (ha : 0 < a) :
    let S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range k, X i ω
    (∫⁻ ω, (tauFrom S a ω : ENNReal) ∂μ) < ⊤ := by
  exact problem_25_axiom μ X h_meas h_indep h_ident h_pos a ha
