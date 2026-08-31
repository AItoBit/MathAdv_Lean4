import Mathlib

/-!
# Orthonormal eigenvectors imply a symmetric matrix

If a real `n × n` matrix `A` admits an orthonormal family `v : Fin n → EuclideanSpace ℝ (Fin n)`
of `n` eigenvectors, then `A` is symmetric, i.e. `Aᵀ = A`.

The vectors are taken in `EuclideanSpace ℝ (Fin n)` (which is definitionally `Fin n → ℝ`) so that
`Orthonormal ℝ v` refers to the standard Euclidean inner product `⟪x, y⟫ = ∑ k, x k * y k`.
-/

open Matrix

variable {n : ℕ}

/-- The matrix whose `j`-th column is the vector `v j`. -/
def eigenMatrix (v : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => v j i

/-- Orthonormality of `v` says exactly that the matrix of columns `v j` is orthogonal. -/
theorem eigenMatrix_transpose_mul_self
    (v : Fin n → EuclideanSpace ℝ (Fin n)) (hv : Orthonormal ℝ v) :
    (eigenMatrix v)ᵀ * eigenMatrix v = 1 := by
  ext i j
  have hij : (inner ℝ (v i) (v j) : ℝ) = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp hv) i j
  rw [PiLp.inner_apply] at hij
  simp only [RCLike.inner_apply, conj_trivial] at hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eigenMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [← hij]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The eigenvector equations, read as a matrix identity `A * V = V * D`. -/
theorem eigenMatrix_mul_diagonal
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → EuclideanSpace ℝ (Fin n)) (lam : Fin n → ℝ)
    (h_eigen : ∀ i : Fin n, A.mulVec (v i) = (lam i) • v i) :
    A * eigenMatrix v = eigenMatrix v * Matrix.diagonal lam := by
  ext i j
  have h := congrFun (h_eigen j) i
  simp only [Pi.smul_apply, smul_eq_mul] at h
  simp only [Matrix.mul_apply, eigenMatrix, Matrix.of_apply, Matrix.diagonal_apply, mul_ite,
    mul_zero]
  rw [show (∑ x, A i x * (v j) x) = (A *ᵥ (v j)) i from rfl, h, mul_comm]
  simp

/-- **Orthonormal eigenvectors imply a symmetric matrix.**
If the real matrix `A` has an orthonormal family of `n` eigenvectors, then `A` is symmetric. -/
theorem question_9
    (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin n))
    (lam : Fin n → ℝ)
    (h_orthonormal : Orthonormal ℝ v)
    (h_eigen : ∀ i : Fin n, A.mulVec (v i) = (lam i) • v i) :
    A.transpose = A := by
  set V := eigenMatrix v
  have h1 : Vᵀ * V = 1 := eigenMatrix_transpose_mul_self v h_orthonormal
  have h2 : V * Vᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : A * V = V * Matrix.diagonal lam := eigenMatrix_mul_diagonal A v lam h_eigen
  have hA : A = V * Matrix.diagonal lam * Vᵀ := by
    calc A = A * (V * Vᵀ) := by rw [h2, Matrix.mul_one]
    _ = (A * V) * Vᵀ := by rw [Matrix.mul_assoc]
    _ = V * Matrix.diagonal lam * Vᵀ := by rw [h3]
  rw [hA]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.diagonal_transpose]
