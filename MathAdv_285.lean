import Mathlib

open Filter Topology

theorem real_analysis_20 :
    ∃ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      (∀ n, Continuous (f n)) ∧
      (∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x))) ∧
      ¬ Continuous g := by

  let f : ℕ → ℝ → ℝ :=
    fun n x => min 1 ((n : ℝ) * |x|)

  let g : ℝ → ℝ :=
    fun x => if x = 0 then 0 else 1

  refine ⟨f, g, ?_, ?_, ?_⟩

  · intro n
    dsimp [f]
    exact continuous_const.min (continuous_const.mul continuous_abs)

  · intro x
    by_cases hx : x = 0

    · subst x
      simp [f, g]

    · have hxabs : 0 < |x| := by
        exact abs_pos.mpr hx

      let N : ℕ := ⌈(1 / |x| : ℝ)⌉₊

      have hceil :
          (1 / |x| : ℝ) ≤ (N : ℝ) := by
        dsimp [N]
        exact Nat.le_ceil (1 / |x| : ℝ)

      have heq :
          (fun n : ℕ => f n x) =ᶠ[atTop]
            (fun _ : ℕ => (1 : ℝ)) := by
        filter_upwards
          [eventually_atTop.2
            ⟨N, fun n hn => hn⟩]
          with n hn

        have hcast :
            (N : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hn

        have hdiv :
            (1 / |x| : ℝ) ≤ (n : ℝ) := by
          exact le_trans hceil hcast

        have hone :
            (1 : ℝ) ≤ (n : ℝ) * |x| := by
          exact (div_le_iff₀ hxabs).mp hdiv

        dsimp [f]
        rw [min_eq_left hone]

      have ht :
          Tendsto (fun n : ℕ => f n x) atTop (nhds (1 : ℝ)) := by
        exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

      simpa [g, hx] using ht

  · intro hg

    have hg0 : ContinuousAt g 0 :=
      hg.continuousAt

    rw [Metric.continuousAt_iff] at hg0

    obtain ⟨δ, hδ, hδprop⟩ :=
      hg0 (1 / 2 : ℝ) (by norm_num)

    let y : ℝ := δ / 2

    have hypos : 0 < y := by
      dsimp [y]
      linarith

    have hyne : y ≠ 0 := by
      exact ne_of_gt hypos

    have hydist :
        dist y 0 < δ := by
      rw [Real.dist_eq]
      simp only [sub_zero]
      rw [abs_of_pos hypos]
      dsimp [y]
      linarith

    have hbad :=
      hδprop hydist

    have hg0val : g 0 = 0 := by
      simp [g]

    have hgy : g y = 1 := by
      simp [g, hyne]

    rw [hgy, hg0val] at hbad
    norm_num [Real.dist_eq] at hbad
