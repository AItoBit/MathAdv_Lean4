import Mathlib

theorem real_analysis_17
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X → X)
    (h : ∀ u v : X, u ≠ v → dist (f u) (f v) < dist u v) :
    ∃ x : X, f x = x := by

  -- The strict contraction assumption implies that f is 1-Lipschitz.
  have hf_lip : LipschitzWith 1 f := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    simp only [NNReal.coe_one, one_mul]
    by_cases huv : u = v
    · subst v
      simp
    · exact le_of_lt (h u v huv)

  have hf_cont : Continuous f :=
    hf_lip.continuous

  -- Consider the displacement function x ↦ dist x (f x).
  let g : X → ℝ := fun x => dist x (f x)

  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_id.dist hf_cont

  -- By compactness, g attains its minimum.
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_univ.exists_isMinOn
      Set.univ_nonempty
      hg_cont.continuousOn

  refine ⟨x, ?_⟩

  by_contra hfix

  have hxf : x ≠ f x := by
    intro hxf
    apply hfix
    exact hxf.symm

  -- Strict contraction makes the displacement at f x
  -- strictly smaller than the minimum displacement at x.
  have hstrict :
      g (f x) < g x := by
    dsimp [g]
    exact h x (f x) hxf

  -- But x minimizes g on all of X.
  have hle :
      g x ≤ g (f x) := by
    exact hmin (Set.mem_univ (f x))

  exact (not_lt_of_ge hle) hstrict
