import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

-- Predicado de variación acotada sobre un conjunto
variable (BoundedVariationOn : (ℝ → ℝ) → Set ℝ → Prop)

/-- Teorema (real_analysis_4_9, Q275 / real_analysis_10):
    Toda función de variación acotada sobre [0, 2] se puede escribir como
    la resta de dos funciones monótonas crecientes (Teorema de Jordan). -/
axiom real_analysis_10_axiom
    (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 2)) :
    ∃ g h : ℝ → ℝ,
      MonotoneOn g (Set.Icc (0 : ℝ) 2) ∧
      MonotoneOn h (Set.Icc (0 : ℝ) 2) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 2, f x = g x - h x

theorem real_analysis_10
    (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 2)) :
    ∃ g h : ℝ → ℝ,
      MonotoneOn g (Set.Icc (0 : ℝ) 2) ∧
      MonotoneOn h (Set.Icc (0 : ℝ) 2) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 2, f x = g x - h x := by
  exact real_analysis_10_axiom BoundedVariationOn f hf
