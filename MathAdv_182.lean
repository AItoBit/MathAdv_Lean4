import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- A `3 × 3` matrix is upper triangular when all entries strictly below the
diagonal vanish. -/
def IsUpperTriangular3x3 (B : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, (i.1 > j.1) → B i j = 0

/-- A `3 × 3` matrix is (unit) lower triangular when all entries strictly above the
diagonal vanish (and the diagonal entries are `1`). -/
def IsUnitLowerTriangular3x3 (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ i j : Fin 3, (i.1 < j.1) → M i j = 0) ∧ (∀ i : Fin 3, M i i = 1)

/-- The matrix `A` of the problem factors as `M * B` with `B` upper triangular. -/
theorem question_12 :
  (let A : Matrix (Fin 3) (Fin 3) ℝ :=
     !![ 9, 0, 0;
         0, 1, 0;
         0, 2, 8 ]
   ∃ M B : Matrix (Fin 3) (Fin 3) ℝ,
     IsUpperTriangular3x3 B ∧
     A = M * B) := by
  intro A
  refine ⟨!![1, 0, 0; 0, 1, 0; 0, 2, 1], !![9, 0, 0; 0, 1, 0; 0, 0, 8], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · show A = _
    simp only [A, Matrix.mul_fin_three]
    norm_num

/-- The stronger statement: `A = M * B` is in fact an `LU` decomposition, i.e. `M`
can be taken unit lower triangular and `B` upper triangular. -/
theorem question_12_LU :
  (let A : Matrix (Fin 3) (Fin 3) ℝ :=
     !![ 9, 0, 0;
         0, 1, 0;
         0, 2, 8 ]
   ∃ M B : Matrix (Fin 3) (Fin 3) ℝ,
     IsUnitLowerTriangular3x3 M ∧
     IsUpperTriangular3x3 B ∧
     A = M * B) := by
  intro A
  refine ⟨!![1, 0, 0; 0, 1, 0; 0, 2, 1], !![9, 0, 0; 0, 1, 0; 0, 0, 8], ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · show A = _
    simp only [A, Matrix.mul_fin_three]
    norm_num

/-- Answer to the multiple-choice question: Cholesky factorization cannot be used,
because it applies only to symmetric matrices, and `A` is not symmetric. -/
theorem question_12_not_symmetric :
  (let A : Matrix (Fin 3) (Fin 3) ℝ :=
     !![ 9, 0, 0;
         0, 1, 0;
         0, 2, 8 ]
   Aᵀ ≠ A) := by
  intro A h
  have h1 : (Aᵀ) 1 2 = A 1 2 := by rw [h]
  simp [A, Matrix.transpose_apply] at h1
