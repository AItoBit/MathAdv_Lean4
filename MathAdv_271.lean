import Mathlib

theorem real_analysis_6 :
  ∃ f : ℝ → ℝ,
    Continuous f ∧
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 0) ∧
    (∀ x ∈ Set.Icc (2 : ℝ) 3, f x = 1) := by
  let f : ℝ → ℝ := fun x => max 0 (min 1 (x - 1))

  refine ⟨f, ?_, ?_, ?_, ?_⟩

  · -- continuity
    dsimp [f]
    exact continuous_const.max
      (continuous_const.min (continuous_id.sub continuous_const))

  · -- range is contained in [0,1]
    intro x
    constructor
    · dsimp [f]
      exact le_max_left 0 (min 1 (x - 1))
    · dsimp [f]
      apply max_le
      · norm_num
      · exact min_le_left 1 (x - 1)

  · -- f = 0 on [0,1]
    intro x hx
    dsimp [f]
    have hx1 : x - 1 ≤ 0 := by
      linarith [hx.2]
    have hmin : min (1 : ℝ) (x - 1) ≤ 0 := by
      exact le_trans (min_le_right 1 (x - 1)) hx1
    exact max_eq_left hmin

  · -- f = 1 on [2,3]
    intro x hx
    dsimp [f]
    have hx1 : (1 : ℝ) ≤ x - 1 := by
      linarith [hx.1]
    rw [min_eq_left hx1]
    norm_num
