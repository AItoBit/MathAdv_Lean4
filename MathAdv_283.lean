import Mathlib

theorem real_analysis_18
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧ f c = 0 := by

  have hzero :
      (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor
    · exact le_of_lt h0
    · exact le_of_lt h1

  obtain ⟨c, hc, hfc⟩ :=
    intermediate_value_Icc
      (show (0 : ℝ) ≤ 1 by norm_num)
      hcont
      hzero

  refine ⟨c, ?_, hfc⟩

  constructor

  · have hc0 : 0 ≤ c := hc.1
    have hcne : c ≠ 0 := by
      intro hceq
      subst c
      linarith
    exact lt_of_le_of_ne hc0 (Ne.symm hcne)

  · have hc1 : c ≤ 1 := hc.2
    have hcne : c ≠ 1 := by
      intro hceq
      subst c
      linarith
    exact lt_of_le_of_ne hc1 hcne
