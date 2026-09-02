import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q269 / real_analysis_4):
    Toda función continua sobre el intervalo compacto [-π, π] está acotada. -/
theorem real_analysis_4 (f : ℝ → ℝ)
    (h : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ C := by
  have h_compact : IsCompact (f '' Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.image_of_continuousOn h
  rcases (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp h_compact.isBounded with ⟨r, hr⟩
  use max r 0
  intro x hx
  have hfx : f x ∈ f '' Set.Icc (-Real.pi) Real.pi := Set.mem_image_of_mem f hx
  have hr' := hr hfx
  rw [Metric.mem_ball, Real.dist_0_eq_abs] at hr'
  exact le_trans (le_of_lt hr') (le_max_left r 0)
