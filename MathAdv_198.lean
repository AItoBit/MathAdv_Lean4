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

/-- Any co-finite subset `Y` of `ℕ` is a finite union of a terminal segment `{x | k ≤ x}`
with a finite set `F`.  This is the key structural fact behind the definability of
co-finite subsets in the structure `(ℕ, <, =)`: such a set is definable by a formula
built from the (definable) terminal segment together with finitely many singletons. -/
theorem open_logic_8 :
  ∀ (Y : Set ℕ), (Yᶜ).Finite → ∃ k : ℕ, ∃ F : Finset ℕ, Y = {x | k ≤ x} ∪ (↑F : Set ℕ) := by
  intro Y hY
  classical
  set S : Finset ℕ := hY.toFinset with hS
  refine ⟨S.sup id + 1, (Finset.range (S.sup id + 1)).filter (fun x => x ∈ Y), ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range,
    Set.mem_setOf_eq]
  constructor
  · intro hx
    by_cases h : S.sup id + 1 ≤ x
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hx⟩
  · rintro (h | ⟨-, h⟩)
    · by_contra hxY
      have hxS : x ∈ S := by simp [hS, Set.mem_compl_iff, hxY]
      have := Finset.le_sup (f := id) hxS
      simp only [id] at this
      omega
    · exact h
