import Mathlib

/-!
# Tangent plane to the implicit surface `x*y*z - 24 = 0` at `(4,2,3)`

For `F x y z = x*y*z - 24` the gradient at `(4,2,3)` is
`(y*z, x*z, x*y) = (6, 12, 8)`, so the tangent plane is
`6*(x - 4) + 12*(y - 2) + 8*(z - 3) = 0`,
equivalently `6*x + 12*y + 8*z = 72 = 24 + 24 + 24`.
-/

/-- The tangent plane equation in point form is equivalent to
`x*(2*3) + (4*y)*3 + (4*2)*z = 24 + 24 + 24`, i.e. `6x + 12y + 8z = 72`. -/
theorem strang_13_3_13 {x y z : ℝ} :
    6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 ↔
      (x * 2 * 3 + 4 * y * 3 + 4 * 2 * z = 24 + 24 + 24) := by
  constructor <;> intro h <;> linarith



/-- The original form of the statement, with `24 + 24` on the right, is false:
at the point `(4,2,3)` of the surface the left side holds but the right side fails. -/
theorem strang_13_3_13_original_false :
    ¬ (∀ x y z : ℝ,
        6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 ↔
          (x * 2 * 3 + 4 * y * 3 + 4 * 2 * z = 24 + 24)) := by
  intro h
  have := (h 4 2 3).mp (by norm_num)
  norm_num at this

/-- The tangent plane at `(4,2,3)` to the surface `x*y*z = 24`, in the standard
implicit-surface form `∇F(P) ⬝ (X - P) = 0`. -/
theorem strang_13_3_13_gradient_form {x y z : ℝ} :
    (2 * 3) * (x - 4) + (4 * 3) * (y - 2) + (4 * 2) * (z - 3) = 0 ↔
      6 * (x - 4) + 12 * (y - 2) + 8 * (z - 3) = 0 := by
  constructor <;> intro h <;> linarith

  have := (h 4 2 3).mp (by norm_num)
  norm_num at this

end Strang13_3_13
