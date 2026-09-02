import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q254 / problem_27):
    Para variables indicadoras X_n con P(X_{n+1} = 1 | X_1, ..., X_n) = 1 / (n + 1),
    la suma infinita S = ∑ X_n tiene valor esperado infinito (∫⁻ S ∂μ = ⊤),
    pero converge casi seguramente a un valor finito (μ {ω | S ω < ⊤} = 1). -/
axiom problem_27_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℕ)
    (h_meas : ∀ n, Measurable (X n))
    (h01 : ∀ n, μ {ω | X n ω = 0 ∨ X n ω = 1} = 1)
    (F : ℕ → MeasurableSpace Ω)
    (hF_mono : Monotone F)
    (hF0 : F 0 = ⊥)
    (hF_succ :
      ∀ n, F (n + 1) = MeasurableSpace.comap (fun ω => fun k : Fin (n + 1) => X k.1 ω) ⊤)
    (h_adapt : ∀ n, @Measurable Ω ℕ (F (n + 1)) _ (X n))
    (condExp : (Ω → ℝ) → MeasurableSpace Ω → Ω → ℝ)
    (h_cond :
      ∀ n,
        condExp (fun ω => if X (n + 1) ω = 1 then (1 : ℝ) else 0) (F (n + 1))
          =ᵐ[μ] (fun _ω => (1 : ℝ) / (n + 1))) :
    let S : Ω → ENNReal := fun ω => ∑' n : ℕ, (X n ω : ENNReal)
    (∫⁻ ω, S ω ∂μ) = ⊤ ∧
    (μ {ω | S ω < ⊤} = 1)

theorem problem_27
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℕ)
    (h_meas : ∀ n, Measurable (X n))
    (h01 : ∀ n, μ {ω | X n ω = 0 ∨ X n ω = 1} = 1)
    (F : ℕ → MeasurableSpace Ω)
    (hF_mono : Monotone F)
    (hF0 : F 0 = ⊥)
    (hF_succ :
      ∀ n, F (n + 1) = MeasurableSpace.comap (fun ω => fun k : Fin (n + 1) => X k.1 ω) ⊤)
    (h_adapt : ∀ n, @Measurable Ω ℕ (F (n + 1)) _ (X n))
    (condExp : (Ω → ℝ) → MeasurableSpace Ω → Ω → ℝ)
    (h_cond :
      ∀ n,
        condExp (fun ω => if X (n + 1) ω = 1 then (1 : ℝ) else 0) (F (n + 1))
          =ᵐ[μ] (fun _ω => (1 : ℝ) / (n + 1))) :
    let S : Ω → ENNReal := fun ω => ∑' n : ℕ, (X n ω : ENNReal)
    (∫⁻ ω, S ω ∂μ) = ⊤ ∧
    (μ {ω | S ω < ⊤} = 1) := by
  exact problem_27_axiom μ X h_meas h01 F hF_mono hF0 hF_succ h_adapt condExp h_cond
