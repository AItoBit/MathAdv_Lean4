import Mathlib

open Filter Topology

theorem real_analysis_3 {x : ℕ → ℝ} {c : ℝ}
    (h : ∀ n, |x n| ≤ c) :
    ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      ∃ l : ℝ, ∀ ε > 0, ∃ N, ∀ n > N,
        |x (phi n) - l| < ε := by
  have hx : ∀ n, x n ∈ Set.Icc (-c) c := by
    intro n
    exact (abs_le.mp (h n))

  have hcompact : IsCompact (Set.Icc (-c) c) :=
    isCompact_Icc

  obtain ⟨l, hl, phi, hphi, hlim⟩ :=
    hcompact.tendsto_subseq hx

  refine ⟨phi, hphi, l, ?_⟩
  intro ε hε

  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hlim) ε hε

  refine ⟨N, ?_⟩
  intro n hn

  have hn' : N ≤ n :=
    Nat.le_of_lt hn

  have hd := hN n hn'

  simpa [Function.comp_apply, Real.dist_eq] using hd
