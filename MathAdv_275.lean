import Mathlib

theorem real_analysis_10
    (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 2)) :
  ∃ g h : ℝ → ℝ,
    MonotoneOn g (Set.Icc (0 : ℝ) 2) ∧
    MonotoneOn h (Set.Icc (0 : ℝ) 2) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 2, f x = g x - h x := by

  have hlocal :
      LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 2) :=
    hf.locallyBoundedVariationOn

  obtain ⟨g, h, hg, hh, hfh⟩ :=
    hlocal.exists_monotoneOn_sub_monotoneOn

  refine ⟨g, h, hg, hh, ?_⟩
  intro x hx

  have hx_eq := congrFun hfh x
  exact hx_eq
