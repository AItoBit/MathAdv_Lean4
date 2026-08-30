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

/-- **Weak boundedness implies norm boundedness.**
If `S` is a subset of a real normed space `X` such that `{f x : x ∈ S}` is bounded for every
continuous linear functional `f ∈ X*`, then `S` is norm-bounded.

The proof applies the uniform boundedness principle (Banach–Steinhaus) to the family of
evaluation functionals `x ∈ S`, viewed as elements of the double dual, acting on the
Banach space `X*`. -/
theorem bollobas_5_18
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (S : Set X)
  (h : ∀ f : X →L[ℝ] ℝ, ∃ C : ℝ, ∀ x ∈ S, |f x| ≤ C) :
  ∃ K : ℝ, ∀ x ∈ S, ‖x‖ ≤ K := by
  set g : S → StrongDual ℝ (StrongDual ℝ X) :=
    fun x => NormedSpace.inclusionInDoubleDual ℝ X x with hg
  have hpt : ∀ f : StrongDual ℝ X, ∃ C : ℝ, ∀ i : S, ‖g i f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := h f
    exact ⟨C, fun i => by simpa [hg, NormedSpace.dual_def, Real.norm_eq_abs] using hC i i.2⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  refine ⟨C', fun x hx => ?_⟩
  have hx' := hC' ⟨x, hx⟩
  rwa [show ‖g ⟨x, hx⟩‖ = ‖x‖ from
    (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).norm_map x] at hx'
