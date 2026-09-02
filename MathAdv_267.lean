import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q267 / real_analysis_2):
    Todo conjunto compacto en ℝ es cerrado y acotado. -/
theorem real_analysis_2 {s : Set ℝ}
    (hs : IsCompact s) :
    IsClosed s ∧ ∃ b : ℝ, ∀ x ∈ s, |x| ≤ b := by
  refine ⟨hs.isClosed, ?_⟩
  rcases (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hs.isBounded with ⟨r, hr⟩
  use max r 0
  intro x hx
  have hx' := hr hx
  rw [Metric.mem_ball, Real.dist_0_eq_abs] at hx'
  exact le_trans (le_of_lt hx') (le_max_left r 0)
