import Mathlib

/-!
# Rank factorization of a 3 × 4 matrix

The matrix
```
A = ![![9, 0, 0, 7],
     ![0, 1, 0, 0],
     ![0, 2, 0, 0]]
```
has rank 2, so it factors as `A = B * C` with `B : Matrix (Fin 3) (Fin 2) ℝ` and
`C : Matrix (Fin 2) (Fin 4) ℝ`.  (Such a decomposition is what an SVD-type
factorization provides; `A` is not square, so Cholesky, LU and eigendecomposition
do not apply.)
-/

theorem question_14 :
  let A : Matrix (Fin 3) (Fin 4) ℝ :=
    ![
      ![9, 0, 0, 7],
      ![0, 1, 0, 0],
      ![0, 2, 0, 0]
    ]
  ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin 4) ℝ), B * C = A := by
  intro A
  refine ⟨![![1, 0], ![0, 1], ![0, 2]], ![![9, 0, 0, 7], ![0, 1, 0, 0]], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
