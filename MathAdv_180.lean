import Mathlib

open Polynomial

theorem question_10 :
    Matrix.charpoly (R := ℝ)
        ![
          ![-7, 8],
          ![-16, 17]
        ]
      = X ^ 2 - 10 * X + 9 := by
  change Matrix.charpoly (![![(-7 : ℝ), 8], ![-16, 17]] : Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  dsimp
  simp only [map_neg, map_add, map_sub, map_mul, map_ofNat]
  ring
