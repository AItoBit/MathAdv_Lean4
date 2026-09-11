import Mathlib

theorem real_analysis_5 {x : ℕ → ℝ} {c : ℝ}
    (h_bound : ∀ n, x n ≤ c)
    (h_mono : ∀ n, x n ≤ x (n + 1)) :
  ∃ l, ∀ ε > 0, ∃ N, ∀ n > N, |x n - l| < ε := by

  have hmono : Monotone x := by
    exact monotone_nat_of_le_succ h_mono

  have hbdd : BddAbove (Set.range x) := by
    refine ⟨c, ?_⟩
    rintro y ⟨n, rfl⟩
    exact h_bound n

  have hne : (Set.range x).Nonempty := by
    exact Set.range_nonempty x

  let l : ℝ := sSup (Set.range x)

  refine ⟨l, ?_⟩
  intro ε hε

  have hx_le : ∀ n, x n ≤ l := by
    intro n
    dsimp [l]
    exact le_csSup hbdd ⟨n, rfl⟩

  have hex : ∃ N, l - ε < x N := by
    by_contra h
    push_neg at h

    have hl : l ≤ l - ε := by
      dsimp [l]
      apply csSup_le hne
      rintro y ⟨n, rfl⟩
      exact h n

    linarith

  obtain ⟨N, hN⟩ := hex

  refine ⟨N, ?_⟩
  intro n hn

  have hNn : N ≤ n := Nat.le_of_lt hn
  have hxn_lower : l - ε < x n := by
    exact lt_of_lt_of_le hN (hmono hNn)

  have hxn_upper : x n ≤ l := hx_le n

  rw [abs_of_nonpos]
  · linarith
  · linarith
