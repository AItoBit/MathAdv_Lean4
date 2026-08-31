import Mathlib

/-!
# Inverse of a unipotent upper-triangular 4×4 matrix

Given
`A = !![1, -a, 0, 0; 0, 1, -b, 0; 0, 0, 1, -c; 0, 0, 0, 1]`
we show its inverse is
`!![1, a, a*b, a*b*c; 0, 1, b, b*c; 0, 0, 1, c; 0, 0, 0, 1]`.
-/

variable {K : Type*} [Field K]

def A (a b c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![ 1, -a,  0,  0;
      0,  1, -b,  0;
      0,  0,  1, -c;
      0,  0,  0,  1]

def Ainv (a b c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![ 1,  a,  a*b,  a*b*c;
      0,  1,    b,    b*c;
      0,  0,    1,      c;
      0,  0,    0,      1]

/-- `Ainv` is a right inverse of `A`. -/
theorem A_mul_Ainv (a b c : K) : A a b c * Ainv a b c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Ainv, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm, mul_left_comm]

/-- The inverse of `A` is `Ainv`. -/
theorem question_7 (a b c : K) :
    (A a b c)⁻¹ = Ainv a b c :=
  Matrix.inv_eq_right_inv (A_mul_Ainv a b c)
