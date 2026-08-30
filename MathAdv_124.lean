import Mathlib

open MeasureTheory

/-- The truncation of a locally integrable function at level `N` is integrable:
if `g_L(x) = f x` for `|x| ≤ L` and `0` otherwise is integrable, then its
truncation to `[-N, N]` is integrable as well.

The hypothesis `0 < L` is kept as stated in the problem, although the proof does not
need it. -/
theorem melrose_sp2009_4
  (f : ℝ → ℝ)
  (L N : ℝ) (hL : 0 < L) (hN : 0 < N)
  (h_int : MeasureTheory.Integrable
    (fun x => if |x| ≤ L then f x else 0) volume) :
  MeasureTheory.Integrable
    (fun x =>
      let gL := if |x| ≤ L then f x else 0
      if gL ≤ N ∧ gL ≥ -N then gL else if gL > N then N else -N)
    volume := by
  have hmeas : AEStronglyMeasurable
      (fun x => max (-N) (min (if |x| ≤ L then f x else 0) N)) volume :=
    (aemeasurable_const.max
      (h_int.aestronglyMeasurable.aemeasurable.min aemeasurable_const)).aestronglyMeasurable
  have key : ∀ x : ℝ,
      (let gL := if |x| ≤ L then f x else 0
       if gL ≤ N ∧ gL ≥ -N then gL else if gL > N then N else -N)
        = max (-N) (min (if |x| ≤ L then f x else 0) N) := by
    intro x
    set g := if |x| ≤ L then f x else 0 with hg
    simp only []
    rcases le_or_gt g N with h1 | h1
    · rcases le_or_gt (-N) g with h2 | h2
      · rw [if_pos ⟨h1, h2⟩, min_eq_left h1, max_eq_right h2]
      · rw [if_neg (by exact fun h => absurd h.2 (not_le.mpr h2)),
          if_neg (by exact not_lt.mpr h1), min_eq_left h1,
          max_eq_left (le_of_lt h2)]
    · rw [if_neg (by exact fun h => absurd h.1 (not_le.mpr h1)), if_pos h1,
        min_eq_right (le_of_lt h1), max_eq_right (by linarith)]
  simp only [key]
  refine Integrable.mono' h_int.norm hmeas ?_
  filter_upwards with x
  set g := if |x| ≤ L then f x else 0 with hg
  rcases le_or_gt g N with h1 | h1
  · rcases le_or_gt (-N) g with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2]
    · rw [min_eq_left h1, max_eq_left (le_of_lt h2)]
      simp only [Real.norm_eq_abs, abs_neg, abs_of_pos hN]
      rw [abs_of_neg (by linarith)]
      linarith
  · rw [min_eq_right (le_of_lt h1), max_eq_right (by linarith)]
    simp only [Real.norm_eq_abs, abs_of_pos hN]
    rw [abs_of_pos (by linarith)]
    linarith

#print axioms melrose_sp2009_4
