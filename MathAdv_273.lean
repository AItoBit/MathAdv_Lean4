import Mathlib

theorem real_analysis_8 :
  ∀ ε : ℝ, ε > 0 →
    ∃ p : Polynomial ℝ,
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        abs (Polynomial.eval x p - abs x) < ε := by
  intro ε hε

  have hcont :
      ContinuousOn (fun x : ℝ => abs x) (Set.Icc (-1 : ℝ) 1) := by
    exact continuous_abs.continuousOn

  exact exists_polynomial_near_of_continuousOn
    (-1 : ℝ) 1
    (fun x : ℝ => abs x)
    hcont
    ε
    hε
