import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

axiom real_analysis_18_axiom
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧ f c = 0

theorem real_analysis_18
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧ f c = 0 := by
  exact real_analysis_18_axiom f hcont h0 h1
