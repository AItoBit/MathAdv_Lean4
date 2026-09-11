import Mathlib

open Filter Topology

theorem real_analysis_9
    (f : ℕ → ℝ → ℝ)
    (hBound : ∃ M : ℝ, ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → |f n x| ≤ M)
    (hEquicont :
      ∀ ε > 0, ∃ δ > 0, ∀ n x y,
        x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |x - y| < δ → |f n x - f n y| < ε) :
  ∃ phi : ℕ → ℕ, StrictMono phi ∧
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Set.Icc (0 : ℝ) 1) ∧
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |f (phi n) x - g x| < ε) := by

  let K : Set ℝ := Set.Icc (0 : ℝ) 1

  obtain ⟨M, hM⟩ := hBound

  have hfcont : ∀ n, ContinuousOn (f n) K := by
    intro n
    rw [Metric.continuousOn_iff]
    intro x hx ε hε

    obtain ⟨δ, hδ, hδprop⟩ := hEquicont ε hε

    refine ⟨δ, hδ, ?_⟩
    intro y hy hxy

    have hyx : |y - x| < δ := by
      simpa [Real.dist_eq] using hxy

    have hval :=
      hδprop n y x hy hx hyx

    simpa [Real.dist_eq] using hval

  let F : ℕ → BoundedContinuousFunction K ℝ :=
    fun n =>
      BoundedContinuousFunction.mkOfCompact
        ⟨K.domRestrict (f n), (hfcont n).domRestrict⟩

  have hF_apply :
      ∀ n (x : K), F n x = f n x := by
    intro n x
    simp [F]

  let A : Set (BoundedContinuousFunction K ℝ) :=
    Set.range F

  have hEq :
      Equicontinuous (fun u : A => (u.1 : K → ℝ)) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε

    obtain ⟨δ, hδ, hδprop⟩ := hEquicont ε hε

    refine ⟨δ, hδ, ?_⟩
    intro y hy u

    rcases u with ⟨u, hu⟩
    rcases hu with ⟨n, rfl⟩

    have hxy_dist :
        dist (x : ℝ) (y : ℝ) < δ := by
      change dist (x : ℝ) (y : ℝ) < δ at hy
      exact hy

    have hxy :
        |(x : ℝ) - (y : ℝ)| < δ := by
      simpa [Real.dist_eq] using hxy_dist

    have hval :
        |f n (x : ℝ) - f n (y : ℝ)| < ε :=
      hδprop n (x : ℝ) (y : ℝ)
        x.property y.property hxy

    simpa [Real.dist_eq, hF_apply] using hval

  have hRange :
      ∀ (u : BoundedContinuousFunction K ℝ) (x : K),
        u ∈ A → u x ∈ Set.Icc (-M) M := by
    intro u x hu
    obtain ⟨n, rfl⟩ := hu

    have hb : |f n x| ≤ M :=
      hM n x x.property

    have hb' : -M ≤ f n x ∧ f n x ≤ M :=
      abs_le.mp hb

    simpa [hF_apply] using hb'

  have hcompact :
      IsCompact (closure A) := by
    exact
      BoundedContinuousFunction.arzela_ascoli
        (Set.Icc (-M) M)
        isCompact_Icc
        A
        hRange
        hEq

  have hmem : ∀ n, F n ∈ closure A := by
    intro n
    apply subset_closure
    exact ⟨n, rfl⟩

  obtain ⟨G, hG, phi, hphi, hlim⟩ :=
    hcompact.tendsto_subseq hmem

  let g : ℝ → ℝ :=
    fun x =>
      if hx : x ∈ K then
        G ⟨x, hx⟩
      else
        0

  have hgK :
      ∀ x (hx : x ∈ K), g x = G ⟨x, hx⟩ := by
    intro x hx
    simp [g, hx]

  have hgcont : ContinuousOn g K := by
    rw [continuousOn_iff_continuous_domRestrict]

    have heq :
        K.domRestrict g = fun x : K => G x := by
      funext x
      exact hgK x x.property

    rw [heq]
    exact G.continuous

  refine ⟨phi, hphi, g, hgcont, ?_⟩

  intro ε hε

  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hlim) ε hε

  refine ⟨N, ?_⟩
  intro n hn x hx

  have hfun :
      dist (F (phi n)) G < ε := by
    exact hN n hn

  let xx : K := ⟨x, hx⟩

  have hpoint :
      dist (F (phi n) xx) (G xx) < ε := by
    exact lt_of_le_of_lt
      (BoundedContinuousFunction.dist_coe_le_dist xx)
      hfun

  have hFx :
      F (phi n) xx = f (phi n) x := by
    exact hF_apply (phi n) xx

  have hgx :
      g x = G xx := by
    simpa [xx] using hgK x hx

  rw [hFx, ← hgx] at hpoint
  simpa [Real.dist_eq] using hpoint
