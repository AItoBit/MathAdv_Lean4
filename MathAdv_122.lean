import Mathlib

/-!
# Continuity of the norm

The norm on any normed space is continuous. The key ingredient is the triangle
inequality, which yields the reverse triangle inequality
`| ‖x‖ - ‖y‖ | ≤ ‖x - y‖`, i.e. the norm is 1-Lipschitz, hence continuous.
-/

/-- The norm is 1-Lipschitz, a direct consequence of the triangle inequality. -/
theorem norm_lipschitzWith_one (E : Type*) [NormedAddCommGroup E] :
    LipschitzWith 1 (fun x : E => ‖x‖) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le x y

/-- The norm on any normed space is continuous. -/
theorem melrose_sp2009_2
  (E : Type*) [NormedAddCommGroup E] :
  Continuous (fun x : E => ‖x‖) :=
  (norm_lipschitzWith_one E).continuous
