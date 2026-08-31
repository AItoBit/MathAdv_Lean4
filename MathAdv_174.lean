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

set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The plane `x - 2y + 3z = 0` in `ℝ³`

The originally proposed statement (`question_4` below) asserts that
`v₁ = (2,1,0)` and `v₂ = (-3,0,1)` form a basis for the **intersection of the plane
with the `xy`-plane**. This is false: `v₂` does not lie in the `xy`-plane (its third
coordinate is `1`), and the intersection of two distinct planes in `ℝ³` is a line,
hence one-dimensional, so it cannot have a two-element basis at all.

We therefore:

* record the original statement, commented out, together with a proof of its
  negation (`question_4_false`);
* prove the two correct statements: `{v₁, v₂}` is a basis of the plane itself
  (`plane_basis`), and `{v₁}` is a basis of the intersection of the plane with the
  `xy`-plane (`plane_inter_xy_basis`).
-/

namespace RequestProject

/-- The plane `x - 2y + 3z = 0`. -/
def P : Set (ℝ × ℝ × ℝ) := { p | p.1 - 2 * p.2.1 + 3 * p.2.2 = 0 }

/-- The `xy`-plane `z = 0`. -/
def XY : Set (ℝ × ℝ × ℝ) := { p | p.2.2 = 0 }

/-- The vector `(2, 1, 0)`. -/
def v₁ : ℝ × ℝ × ℝ := (2, (1, 0))

/-- The vector `(-3, 0, 1)`. -/
def v₂ : ℝ × ℝ × ℝ := (-3, (0, 1))

/-
The original (false) statement:

theorem question_4 :
  let P : Set (ℝ × ℝ × ℝ) :=
    { p | p.1 - 2 * p.2.1 + 3 * p.2.2 = 0 }
  let XY : Set (ℝ × ℝ × ℝ) :=
    { p | p.2.2 = 0 }
  let v₁ : ℝ × ℝ × ℝ := (2, (1, 0))
  let v₂ : ℝ × ℝ × ℝ := (-3, (0, 1))
  ((v₁ ∈ P ∧ v₁ ∈ XY) ∧
   (v₂ ∈ P ∧ v₂ ∈ XY) ∧
   LinearIndependent ℝ ![v₁, v₂] ∧
   (↑(Submodule.span ℝ ({v₁, v₂} : Set (ℝ × ℝ × ℝ))) =
      { p : ℝ × ℝ × ℝ | p ∈ P ∧ p ∈ XY })) := by
  sorry

It is false because `v₂ ∉ XY`: the third coordinate of `v₂` is `1`, not `0`.
-/

/-- The originally proposed statement is false: `v₂ = (-3,0,1)` does not lie in the
`xy`-plane, so `{v₁, v₂}` cannot be a basis of the intersection. -/
theorem question_4_false :
    ¬ (let P : Set (ℝ × ℝ × ℝ) :=
        { p | p.1 - 2 * p.2.1 + 3 * p.2.2 = 0 }
      let XY : Set (ℝ × ℝ × ℝ) :=
        { p | p.2.2 = 0 }
      let v₁ : ℝ × ℝ × ℝ := (2, (1, 0))
      let v₂ : ℝ × ℝ × ℝ := (-3, (0, 1))
      ((v₁ ∈ P ∧ v₁ ∈ XY) ∧
       (v₂ ∈ P ∧ v₂ ∈ XY) ∧
       LinearIndependent ℝ ![v₁, v₂] ∧
       (↑(Submodule.span ℝ ({v₁, v₂} : Set (ℝ × ℝ × ℝ))) =
          { p : ℝ × ℝ × ℝ | p ∈ P ∧ p ∈ XY }))) := by
  intro h
  have h₂ : (1 : ℝ) = 0 := h.2.1.2
  norm_num at h₂

/-- `v₁` and `v₂` are linearly independent over `ℝ`. -/
theorem v₁_v₂_linearIndependent : LinearIndependent ℝ ![v₁, v₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [v₁, v₂, Prod.ext_iff, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk,
    Prod.fst_zero, Prod.snd_zero] at hst
  obtain ⟨-, hs, ht⟩ := hst
  constructor <;> linarith [hs, ht]

/-- `{v₁, v₂}` is a basis of the plane `x - 2y + 3z = 0`: both vectors lie in the
plane, they are linearly independent, and they span it. -/
theorem plane_basis :
    v₁ ∈ P ∧ v₂ ∈ P ∧ LinearIndependent ℝ ![v₁, v₂] ∧
      (↑(Submodule.span ℝ ({v₁, v₂} : Set (ℝ × ℝ × ℝ))) = P) := by
  refine ⟨by simp [P, v₁], by simp [P, v₂], v₁_v₂_linearIndependent, ?_⟩
  ext p
  simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_ofPred_eq, P]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp only [v₁, v₂, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    ring
  · intro hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    simp only [v₁, v₂, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.ext_iff]
    refine ⟨by linarith, by ring, by ring⟩

/-- The intersection of the plane `x - 2y + 3z = 0` with the `xy`-plane is the line
spanned by `v₁ = (2,1,0)`; `{v₁}` is a basis of it. -/
theorem plane_inter_xy_basis :
    (v₁ ∈ P ∧ v₁ ∈ XY) ∧ LinearIndependent ℝ ![v₁] ∧
      (↑(Submodule.span ℝ ({v₁} : Set (ℝ × ℝ × ℝ))) =
        { p : ℝ × ℝ × ℝ | p ∈ P ∧ p ∈ XY }) := by
  refine ⟨⟨by simp [P, v₁], by simp [XY, v₁]⟩, ?_, ?_⟩
  · rw [linearIndependent_unique_iff]
    simp [v₁, Prod.ext_iff]
  · ext p
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_ofPred_eq, P, XY]
    constructor
    · rintro ⟨a, rfl⟩
      simp only [v₁, Prod.smul_mk, smul_eq_mul]
      constructor
      · ring
      · ring
    · rintro ⟨hp, hz⟩
      refine ⟨p.2.1, ?_⟩
      simp only [v₁, Prod.smul_mk, smul_eq_mul, Prod.ext_iff]
      refine ⟨by linarith, by ring, by rw [hz]; ring⟩

/-- Since the intersection is one-dimensional, no two vectors can form a basis for it:
`{v₁, v₂}` is not a basis of the intersection for **any** choice of `v₁, v₂`, because
any two vectors of the intersection are linearly dependent. -/
theorem inter_not_two_dimensional (w₁ w₂ : ℝ × ℝ × ℝ)
    (h₁ : w₁ ∈ P ∧ w₁ ∈ XY) (h₂ : w₂ ∈ P ∧ w₂ ∈ XY) :
    ¬ LinearIndependent ℝ ![w₁, w₂] := by
  rw [LinearIndependent.pair_iff]
  push Not
  obtain ⟨hp₁, hz₁⟩ := h₁
  obtain ⟨hp₂, hz₂⟩ := h₂
  simp only [P, Set.mem_ofPred_eq] at hp₁ hp₂
  simp only [XY, Set.mem_ofPred_eq] at hz₁ hz₂
  by_cases hw₁ : w₁ = 0
  · exact ⟨1, 0, by simp [hw₁], by norm_num⟩
  · refine ⟨w₂.2.1, -w₁.2.1, ?_, ?_⟩
    · have hx₁ : w₁.1 = 2 * w₁.2.1 := by rw [hz₁] at hp₁; linarith
      have hx₂ : w₂.1 = 2 * w₂.2.1 := by rw [hz₂] at hp₂; linarith
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Prod.fst_zero, Prod.snd_zero]
      refine ⟨by rw [hx₁, hx₂]; ring, by ring, by rw [hz₁, hz₂]; ring⟩
    · intro _ h
      apply hw₁
      have hy₁ : w₁.2.1 = 0 := by linarith [neg_eq_zero.mp h]
      have hx₁ : w₁.1 = 0 := by rw [hz₁] at hp₁; linarith
      exact Prod.ext hx₁ (Prod.ext hy₁ hz₁)

/-- The corrected version of the original statement, phrased in the same `let`-bound style.

Two modifications were made to the original:
* `{v₁, v₂}` is a basis of the **plane** `x - 2y + 3z = 0` (not of its intersection with
  the `xy`-plane); this is the null space of the row vector `[1, -2, 3]`.
* the intersection of the plane with the `xy`-plane is the line spanned by `v₁` alone.
-/
theorem question_4_corrected :
    let P : Set (ℝ × ℝ × ℝ) :=
      { p | p.1 - 2 * p.2.1 + 3 * p.2.2 = 0 }
    let XY : Set (ℝ × ℝ × ℝ) :=
      { p | p.2.2 = 0 }
    let v₁ : ℝ × ℝ × ℝ := (2, (1, 0))
    let v₂ : ℝ × ℝ × ℝ := (-3, (0, 1))
    ((v₁ ∈ P ∧ v₂ ∈ P ∧
      LinearIndependent ℝ ![v₁, v₂] ∧
      (↑(Submodule.span ℝ ({v₁, v₂} : Set (ℝ × ℝ × ℝ))) = P)) ∧
     ((v₁ ∈ P ∧ v₁ ∈ XY) ∧
      LinearIndependent ℝ ![v₁] ∧
      (↑(Submodule.span ℝ ({v₁} : Set (ℝ × ℝ × ℝ))) =
        { p : ℝ × ℝ × ℝ | p ∈ P ∧ p ∈ XY }))) :=
  ⟨plane_basis, plane_inter_xy_basis⟩

end RequestProject
