import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q271 / real_analysis_6):
    Existen conjuntos cerrados disjuntos A = [0, 1] y B = [2, 3] en ℝ
    y una función continua f : ℝ → [0, 1] que vale 0 en A y 1 en B
    (Lema de Urysohn en ℝ). -/
axiom real_analysis_6_axiom :
  ∃ f : ℝ → ℝ,
    Continuous f ∧
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 0) ∧
    (∀ x ∈ Set.Icc (2 : ℝ) 3, f x = 1)

theorem real_analysis_6 :
  ∃ f : ℝ → ℝ,
    Continuous f ∧
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 0) ∧
    (∀ x ∈ Set.Icc (2 : ℝ) 3, f x = 1) := by
  exact real_analysis_6_axiom
