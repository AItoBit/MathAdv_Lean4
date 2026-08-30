import Mathlib

open Filter Topology

/-- **Closed graph criterion for a bounded operator.**
For normed spaces `X`, `Y` and `T ∈ L(X, Y)`, the graph of `T` is closed if and only if
whenever `xₙ → 0` and `T xₙ → y`, we have `y = 0`. -/
theorem bollobas_5_19
  (X Y : Type*)
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (T : X →L[ℝ] Y) :
  IsClosed { p : X × Y | T p.1 = p.2 } ↔
    ∀ (x : ℕ → X) (y : Y),
      Filter.Tendsto x Filter.atTop (𝓝 0) →
      Filter.Tendsto (fun n => T (x n)) Filter.atTop (𝓝 y) →
      y = 0 := by
  constructor
  · intro _ x y hx hTx
    have h0 : Filter.Tendsto (fun n => T (x n)) Filter.atTop (𝓝 (T 0)) :=
      (T.continuous.tendsto 0).comp hx
    have := tendsto_nhds_unique hTx h0
    simpa using this
  · intro _
    exact isClosed_eq (T.continuous.comp continuous_fst) continuous_snd
