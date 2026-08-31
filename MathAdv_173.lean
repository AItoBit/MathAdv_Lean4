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

set_option grind.warning false

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-
The originally proposed statement wrote the vector as `(![1, -2, 3] : R3)`.
That does not typecheck in this version of Mathlib: `![1, -2, 3]` is a plain
function `Fin 3 → ℝ`, while `R3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2
(Fin 3 → ℝ)`, which is no longer definitionally that function type.  The
statement below is the same one, with the vector written using the
`EuclideanSpace` tuple notation `!₂[1, -2, 3]`.
-/

/-- The vector `v = [1, -2, 3]ᵀ` spans exactly the orthogonal complement of the
plane `x - 2y + 3z = 0` in `ℝ³`; i.e. `v` is a basis for the vectors
perpendicular to that plane. -/
theorem question_3 :
    Submodule.span ℝ { (!₂[1, -2, 3] : R3) }
      =
    (Submodule.span ℝ { x : R3 | x 0 - 2 * x 1 + 3 * x 2 = 0 })ᗮ := by
  apply le_antisymm
  · rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    rintro u rfl w hw
    have hw' : w 0 - 2 * w 1 + 3 * w 2 = 0 := hw
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    linarith
  · intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    have h1 : (!₂[2, 1, 0] : R3) ∈
        Submodule.span ℝ { x : R3 | x 0 - 2 * x 1 + 3 * x 2 = 0 } := by
      apply Submodule.subset_span
      show (!₂[2, 1, 0] : R3) 0 - 2 * (!₂[2, 1, 0] : R3) 1 + 3 * (!₂[2, 1, 0] : R3) 2 = 0
      simp
    have h2 : (!₂[-3, 0, 1] : R3) ∈
        Submodule.span ℝ { x : R3 | x 0 - 2 * x 1 + 3 * x 2 = 0 } := by
      apply Submodule.subset_span
      show (!₂[-3, 0, 1] : R3) 0 - 2 * (!₂[-3, 0, 1] : R3) 1 + 3 * (!₂[-3, 0, 1] : R3) 2 = 0
      simp
    have e1 := hx _ h1
    have e2 := hx _ h2
    simp [PiLp.inner_apply, Fin.sum_univ_three] at e1 e2
    rw [Submodule.mem_span_singleton]
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith
