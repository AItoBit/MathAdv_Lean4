import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def IsUpperTriangular (B : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ i j, i > j → B i j = 0

theorem question_13 :
  let A : Matrix (Fin 3) (Fin 4) ℝ :=
    ![
      ![9, 0, 0, 7],
      ![0, 1, 0, 0],
      ![0, 2, 8, 3]
    ]
  ∃ (C : Matrix (Fin 3) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ),
    A = C * B ∧ IsUpperTriangular B := by
  intro A
  -- Choose C = A and B = 1 (the 4×4 identity matrix)
  use A, 1
  constructor
  · -- A = A * 1
    exact (Matrix.mul_one A).symm
  · -- Prove 1 is upper triangular
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    exact Matrix.one_apply_ne hne
