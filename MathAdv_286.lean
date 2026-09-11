import Mathlib

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem real_analysis_21
    {𝕜 X Y : Type*}
    [NormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Tn : ℕ → X →L[𝕜] Y)
    (T : X → Y)
    (hconv :
      ∀ x : X,
        Filter.Tendsto
          (fun n => Tn n x)
          Filter.atTop
          (nhds (T x))) :
    ∃ S : X →L[𝕜] Y, ∀ x, S x = T x := by

  have hconv' :
      Filter.Tendsto
        (fun n : ℕ => fun x : X => Tn n x)
        Filter.atTop
        (nhds T) := by
    rw [tendsto_pi_nhds]
    intro x
    exact hconv x

  refine ⟨continuousLinearMapOfTendsto Tn hconv', ?_⟩
  intro x
  rfl
