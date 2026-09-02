import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q272 / real_analysis_7):
    En un espacio métrico completo, toda intersección numerable de abiertos
    densos es densa (Teorema de Categoría de Baire). -/
theorem real_analysis_7 {X : Type*} [MetricSpace X] [CompleteSpace X]
    {U : ℕ → Set X}
    (hU_open : ∀ n, IsOpen (U n))
    (hU_dense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  exact dense_iInter_of_isOpen hU_open hU_dense
