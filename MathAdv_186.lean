import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace OrthogonalComplement

/-- The orthogonal complement of a set `S ⊆ ℝⁿ`, as a bare set:
all vectors orthogonal to every element of `S`. -/
def orthSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {v | ∀ u ∈ S, ⟪u, v⟫_ℝ = 0}

/-- `0` belongs to the orthogonal complement of any set. -/
theorem zero_mem_orthSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ orthSet S := by
  intro u _
  simp

/-- The orthogonal complement is closed under addition. -/
theorem add_mem_orthSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {v w : EuclideanSpace ℝ (Fin n)} (hv : v ∈ orthSet S) (hw : w ∈ orthSet S) :
    v + w ∈ orthSet S := by
  intro u hu
  rw [inner_add_right, hv u hu, hw u hu, add_zero]

/-- The orthogonal complement is closed under scalar multiplication. -/
theorem smul_mem_orthSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (c : ℝ) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ orthSet S) :
    c • v ∈ orthSet S := by
  intro u hu
  rw [real_inner_smul_right, hv u hu, mul_zero]

/-- **`Sᗮ` is a subspace of `ℝⁿ`.** The orthogonal complement of a subspace `S`
(in fact, of an arbitrary set) is itself a subspace of `ℝⁿ`: it contains `0`
and is closed under addition and scalar multiplication. -/
def orthSubmodule {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := orthSet S
  zero_mem' := zero_mem_orthSet S
  add_mem' hv hw := add_mem_orthSet S hv hw
  smul_mem' c _ hv := smul_mem_orthSet S c hv

@[simp] theorem mem_orthSubmodule {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ orthSubmodule S ↔ ∀ u ∈ S, ⟪u, v⟫_ℝ = 0 := Iff.rfl

/-- The subspace just constructed is exactly Mathlib's orthogonal complement `Sᗮ`
of a subspace `S`. -/
theorem orthSubmodule_eq_orthogonal {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    orthSubmodule (S : Set (EuclideanSpace ℝ (Fin n))) = Sᗮ := by
  ext v
  simp [Submodule.mem_orthogonal]

/-- **Main statement: `Sᗮ` is a subspace of `ℝⁿ` whenever `S` is.**
For a subspace `S` of `ℝⁿ`, the orthogonal complement
`S^⊥ = {v | ∀ u ∈ S, ⟪u, v⟫ = 0}` contains `0` and is closed under addition and
under scalar multiplication, i.e. it satisfies the three subspace axioms; the
subspace it forms is exactly `Sᗮ`. -/
theorem orthogonal_isSubspace {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ((0 : EuclideanSpace ℝ (Fin n)) ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ v w : EuclideanSpace ℝ (Fin n),
        v ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n))) →
        w ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n))) →
        v + w ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin n)),
        v ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n))) →
        c • v ∈ orthSet (S : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (orthSet (S : Set (EuclideanSpace ℝ (Fin n))) = (Sᗮ : Set (EuclideanSpace ℝ (Fin n)))) := by
  refine ⟨zero_mem_orthSet _, fun v w hv hw => add_mem_orthSet _ hv hw,
    fun c v hv => smul_mem_orthSet _ c hv, ?_⟩
  have := orthSubmodule_eq_orthogonal S
  exact congrArg (fun T : Submodule ℝ (EuclideanSpace ℝ (Fin n)) =>
    (T : Set (EuclideanSpace ℝ (Fin n)))) this

/-- The original (trivially true) statement as given. -/
theorem question_15
    {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Sᗮ ≤ Sᗮ := le_rfl

end OrthogonalComplement
