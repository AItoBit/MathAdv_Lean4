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

open Matrix in
/-- The row space of `A`, as the set of linear combinations of the rows of `A`. -/
def rowSpaceSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  { v | ∃ c : Fin m → ℝ,
      v = fun j => ∑ i : Fin m, c i * A i j }

open Matrix in
/-- The null space of `A`. -/
def nullSpaceSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  { v | A.mulVec v = 0 }

open Matrix in
/-- The hypothesis that the row space and the null space of `A` coincide. -/
def RowspaceEqNullspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  rowSpaceSet A = nullSpaceSet A

open Matrix in
/-- The row space of `A` is the range of the linear map `c ↦ Aᵀ *ᵥ c`. -/
lemma rowSpaceSet_eq_range_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    rowSpaceSet A = (LinearMap.range (Aᵀ.mulVecLin) : Set (Fin n → ℝ)) := by
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext j; simp [Matrix.vecMul, dotProduct, mul_comm]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext j; simp [Matrix.vecMul, dotProduct, mul_comm]⟩

open Matrix in
/-- The null space of `A` is the kernel of the linear map `v ↦ A *ᵥ v`. -/
lemma nullSpaceSet_eq_ker {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nullSpaceSet A = (LinearMap.ker (A.mulVecLin) : Set (Fin n → ℝ)) := by
  ext v
  simp [nullSpaceSet, LinearMap.mem_ker]

open Matrix in
/-- If the row space and the null space of `A` coincide, then `A` has an even number of
columns.  (Rank–nullity: `n = rank A + nullity A`, and the hypothesis forces
`rank A = nullity A`.) -/
theorem question_20
  {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
  (h : RowspaceEqNullspace A) :
  Even n := by
  have hsub : LinearMap.range (Aᵀ.mulVecLin) = LinearMap.ker (A.mulVecLin) := by
    apply SetLike.coe_injective
    rw [← rowSpaceSet_eq_range_transpose, ← nullSpaceSet_eq_ker]
    exact h
  have hrn : Module.finrank ℝ (LinearMap.range (A.mulVecLin))
      + Module.finrank ℝ (LinearMap.ker (A.mulVecLin)) = n := by
    have := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin)
    simpa using this
  have hrk : Module.finrank ℝ (LinearMap.range (A.mulVecLin))
      = Module.finrank ℝ (LinearMap.ker (A.mulVecLin)) := by
    rw [← hsub]
    exact (Matrix.rank_transpose A).symm
  exact ⟨Module.finrank ℝ (LinearMap.ker (A.mulVecLin)), by omega⟩
