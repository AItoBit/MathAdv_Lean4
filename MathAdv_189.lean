import Mathlib

/-- The matrix
`A = ![![1, 2, -1], ![2, 4, 7], ![-2, -4, 1]]`
is not invertible: its determinant vanishes (the second column is twice the first),
so by the Invertible Matrix Theorem it is not a unit. -/
theorem question_19 :
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
  ![
    ![1, 2, -1],
    ![2, 4, 7],
    ![-2, -4, 1]
  ]
  ¬ IsUnit A := by
  intro A
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : A.det = 0 := by
    rw [Matrix.det_fin_three]
    dsimp [A]
    norm_num
  rw [hdet]
  simp
