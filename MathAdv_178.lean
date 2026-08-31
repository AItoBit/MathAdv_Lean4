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

/-!
# Real symmetric matrices have orthogonal eigenvectors

The relevant theorem is the **Spectral Theorem** (answer (a)).

Formal statement: for a real symmetric `n × n` matrix `A` there is a family of `n` nonzero
eigenvectors `v i` with eigenvalues `μ i` that are pairwise orthogonal (their dot products
vanish).  In fact the eigenvectors produced here form an orthonormal basis of `ℝⁿ`.

Note: the dot product `Matrix.dotProduct` of the informal statement lives in the root namespace
as `dotProduct` in this version of Mathlib, so it is written `dotProduct` below.
-/
theorem question_8
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
  Matrix.transpose A = A →
    ∃ (v : Fin n → (Fin n → ℝ)) (μ : Fin n → ℝ),
      (∀ i, v i ≠ 0 ∧ A.mulVec (v i) = μ i • v i) ∧
      (∀ i j, i ≠ j → dotProduct (v i) (v j) = 0) := by
  intro hsym
  -- Over `ℝ` the conjugate transpose is the transpose, so `A` is Hermitian.
  have hA : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  -- The spectral theorem provides an orthonormal eigenvector basis.
  refine ⟨fun i => ⇑(hA.eigenvectorBasis i), hA.eigenvalues, ?_, ?_⟩
  · intro i
    refine ⟨?_, hA.mulVec_eigenvectorBasis i⟩
    intro h
    have h1 := hA.eigenvectorBasis.orthonormal.1 i
    have h2 : (hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n)) = 0 := by
      ext k
      exact congrFun h k
    rw [h2] at h1
    simp at h1
  · intro i j hij
    have h : inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis j) = 0 :=
      hA.eigenvectorBasis.orthonormal.2 hij
    rw [PiLp.inner_apply] at h
    simpa [dotProduct, mul_comm] using h

#print axioms question_8
