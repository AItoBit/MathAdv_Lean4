import Mathlib

/-!
# Tangent plane to the implicit surface `xyz - 24 = 0` at `(4, 2, 3)`

The surface is the zero level set of `F x y z = x * y * z - 24`.  Its gradient at
`(4, 2, 3)` is `(y*z, x*z, x*y) = (6, 12, 8)`, so the tangent plane at that point is

`6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0`.

(The technique used is "tangent plane to an implicit surface", i.e. option (d).)
-/

namespace Strang13_3_13

/-- The defining function of the surface: `F x y z = x*y*z - 24`. -/
def F (x y z : ℝ) : ℝ := x * y * z - 24

/-- The point `(4, 2, 3)` lies on the surface. -/
theorem F_at_point : F 4 2 3 = 0 := by
  norm_num [F]

/-- Partial derivative of `F` in `x` at `(4,2,3)` is `y*z = 6`. -/
theorem hasDerivAt_F_x : HasDerivAt (fun x : ℝ => F x 2 3) 6 4 := by
  have he : (fun x : ℝ => F x 2 3) = fun x : ℝ => 6 * x - 24 := by
    funext x; simp [F]; ring
  rw [he]
  simpa using ((hasDerivAt_id (4 : ℝ)).const_mul (6 : ℝ)).sub_const 24

/-- Partial derivative of `F` in `y` at `(4,2,3)` is `x*z = 12`. -/
theorem hasDerivAt_F_y : HasDerivAt (fun y : ℝ => F 4 y 3) 12 2 := by
  have he : (fun y : ℝ => F 4 y 3) = fun y : ℝ => 12 * y - 24 := by
    funext y; simp [F]; ring
  rw [he]
  simpa using ((hasDerivAt_id (2 : ℝ)).const_mul (12 : ℝ)).sub_const 24

/-- Partial derivative of `F` in `z` at `(4,2,3)` is `x*y = 8`. -/
theorem hasDerivAt_F_z : HasDerivAt (fun z : ℝ => F 4 2 z) 8 3 := by
  have he : (fun z : ℝ => F 4 2 z) = fun z : ℝ => 8 * z - 24 := by
    funext z; simp only [F]; ring
  rw [he]
  simpa using ((hasDerivAt_id (3 : ℝ)).const_mul (8 : ℝ)).sub_const 24

/-- The linear map `(u, v, w) ↦ 6u + 12v + 8w`, i.e. the gradient of `F` at
`(4, 2, 3)` viewed as a linear functional. -/
noncomputable def gradL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (6 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
  (12 : ℝ) • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
  (8 : ℝ) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

@[simp] theorem gradL_apply (p : ℝ × ℝ × ℝ) :
    gradL p = 6 * p.1 + 12 * p.2.1 + 8 * p.2.2 := by
  simp [gradL]

/-- `F` is differentiable at `(4, 2, 3)` with derivative `(u,v,w) ↦ 6u + 12v + 8w`,
i.e. the gradient of `F` there is `(6, 12, 8)`. -/
theorem hasFDerivAt_F :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) gradL (4, 2, 3) := by
  have hx : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (4, 2, 3) :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hy : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (4, 2, 3) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hz : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (4, 2, 3) :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have h := ((hx.mul hy).mul hz).sub_const (24 : ℝ)
  refine (show HasFDerivAt (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) _ (4, 2, 3) from
    h).congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  simp
  ring

/-- The tangent plane, defined intrinsically as the set of points `p` at which the
derivative of `F` at `(4,2,3)` annihilates `p - (4,2,3)`. -/
def tangentPlane : Set (ℝ × ℝ × ℝ) :=
  {p | gradL (p - (4, 2, 3)) = 0}

/-- **Answer.** The tangent plane to `xyz - 24 = 0` at `(4, 2, 3)` is exactly the
plane `6 (x - 4) + 12 (y - 2) + 8 (z - 3) = 0`. -/
theorem tangentPlane_eq :
    tangentPlane =
      {p : ℝ × ℝ × ℝ | 6 * (p.1 - 4) + 12 * (p.2.1 - 2) + 8 * (p.2.2 - 3) = 0} := by
  ext p
  simp only [tangentPlane, Set.mem_setOf_eq, gradL_apply, Prod.fst_sub, Prod.snd_sub]

/-- Equivalent linear form of the tangent plane equation: `6x + 12y + 8z = 72`. -/
theorem tangentPlane_iff (x y z : ℝ) :
    6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 ↔
      x * 2 * 3 + 4 * y * 3 + 4 * 2 * z = 24 + 24 + 24 := by
  constructor <;> intro h <;> linarith

/-
The statement originally proposed,

theorem strang_13_3_13
  {x y z : ℝ} :
  6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 ↔
  (x * 2 * 3 + 4 * y * 3 + 4 * 2 * z = 24 + 24) := by
sorry

is FALSE: expanding the left-hand side gives `6x + 12y + 8z = 72`, while the
right-hand side reads `6x + 12y + 8z = 48`.  The right-hand constant must be
`24 + 24 + 24 = 72` (each of the three terms contributes `24` at the point
`(4,2,3)`), as in `tangentPlane_iff` above.  The falsity is proved next.
-/

/-- The originally proposed statement is false: it already fails at the point
`(4,2,3)` itself, which certainly lies on the tangent plane. -/
theorem strang_13_3_13_false :
    ¬ ∀ x y z : ℝ,
      (6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 ↔
        x * 2 * 3 + 4 * y * 3 + 4 * 2 * z = 24 + 24) := by
  intro h
  have := (h 4 2 3).mp (by norm_num)
  norm_num at this

end Strang13_3_13
