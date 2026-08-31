import Mathlib

/-!
# Volume of a Riemannian `k`-fold covering

If `M → N` is a Riemannian `k`-fold covering map, then `vol M = k * vol N`.

The measure-theoretic content is captured by the hypothesis that the pushforward of the
volume measure of `M` under the covering map equals `k` times the volume measure of `N`
(each fibre has `k` points, and the covering is a local isometry). From this the volume
identity follows directly.

The hypothesis `1 ≤ k` is kept as stated in the problem, although the proof does not need it.
-/

theorem Petersen_6_12
    {M N : Type*} [MeasurableSpace M] [MeasurableSpace N]
    (μM : MeasureTheory.Measure M) (μN : MeasureTheory.Measure N)
    [MeasureTheory.IsFiniteMeasure μM] [MeasureTheory.IsFiniteMeasure μN]
    (f : M → N) (hf : Measurable f)
    (k : ℕ) (_hk : 1 ≤ k)
    (hcover : MeasureTheory.Measure.map f μM = (k : ENNReal) • μN) :
    (μM Set.univ).toReal = (k : ℝ) * (μN Set.univ).toReal := by
  have h : μM Set.univ = (k : ENNReal) * μN Set.univ := by
    have := congrArg (fun m => m Set.univ) hcover
    simpa [MeasureTheory.Measure.map_apply hf MeasurableSet.univ] using this
  rw [h, ENNReal.toReal_mul]
  simp
