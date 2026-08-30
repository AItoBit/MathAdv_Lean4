import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- **Distance to a closed subspace is attained.**

Let `Y` be a closed subspace of a complete real inner product space `X` and let `x ∈ X`.
Then there is `y ∈ Y` with `dist x y = infDist x Y`, i.e. the distance from `x` to `Y`
is attained.  (Note: as formalized, `X` is a real Hilbert space; in a general Banach space
the distance to a closed subspace need not be attained.) -/
theorem bollobas_2_12
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Y : Submodule ℝ X) (hY : IsClosed (Y : Set X)) (x : X) :
    ∃ y : Y, dist x (y : X) = Metric.infDist x (Y : Set X) := by
  obtain ⟨v, hv, hvn⟩ := Y.exists_norm_eq_iInf_of_complete_subspace hY.isComplete x
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [dist_eq_norm, hvn, Metric.infDist_eq_iInf]
  simp [dist_eq_norm]
