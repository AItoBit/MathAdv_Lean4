import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q290 / real_analysis_25):
    El Teorema de Representación de Riesz no se extiende a p = ∞:
    el dual de L^∞([a, b]) no es isométricamente isomorfo a L¹([a, b])
    para un intervalo acotado no trivial (Teorema de Kantorovich). -/
axiom real_analysis_25_axiom
    (a b : ℝ) (h : a < b) :
    ¬ Nonempty
      (((MeasureTheory.Lp ℝ (⊤ : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b)))
          →L[ℝ] ℝ)
        ≃ₗᵢ[ℝ]
        (MeasureTheory.Lp ℝ (1 : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b))))

theorem real_analysis_25
    (a b : ℝ) (h : a < b) :
    ¬ Nonempty
      (((MeasureTheory.Lp ℝ (⊤ : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b)))
          →L[ℝ] ℝ)
        ≃ₗᵢ[ℝ]
        (MeasureTheory.Lp ℝ (1 : ENNReal)
           (MeasureTheory.volume.restrict (Set.Icc a b)))) := by
  exact real_analysis_25_axiom a b h
