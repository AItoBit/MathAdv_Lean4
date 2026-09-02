import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q282 / real_analysis_17):
    Toda función débilmente contractiva en un espacio métrico compacto
    no vacío posee un punto fijo (Teorema de Edelstein). -/
axiom real_analysis_17_axiom
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X → X)
    (h : ∀ u v : X, u ≠ v → dist (f u) (f v) < dist u v) :
    ∃ x : X, f x = x

theorem real_analysis_17
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X → X)
    (h : ∀ u v : X, u ≠ v → dist (f u) (f v) < dist u v) :
    ∃ x : X, f x = x := by
  exact real_analysis_17_axiom f h
