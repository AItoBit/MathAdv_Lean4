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

/-- The Euclidean dot product of two vectors in `ℝ³`. -/
def dot (u v : ℝ × ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- The Euclidean norm of a vector in `ℝ³`. -/
noncomputable def norm3 (u : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (dot u u)

/-- The angle (in radians) between two vectors in `ℝ³`,
defined by `θ = arccos (u ⬝ v / (‖u‖ ‖v‖))`. -/
noncomputable def angle3 (u v : ℝ × ℝ × ℝ) : ℝ :=
  Real.arccos (dot u v / (norm3 u * norm3 v))

/-- The vectors `u = 2i - j + 7k` and `v = i + 2j` have zero dot product. -/
theorem question_6 :
    (let u : ℝ × ℝ × ℝ := (2, (-1, 7))
     let v : ℝ × ℝ × ℝ := (1, (2, 0))
     dot u v = 0) := by
  norm_num [dot]

/-- The angle between `u = 2i - j + 7k` and `v = i + 2j` is `π / 2`, i.e. `90°`. -/
theorem angle_u_v_eq_pi_div_two :
    angle3 (2, (-1, 7)) (1, (2, 0)) = Real.pi / 2 := by
  have h : dot ((2 : ℝ), ((-1 : ℝ), (7 : ℝ))) (1, (2, 0)) = 0 := by
    norm_num [dot]
  simp [angle3, h]
