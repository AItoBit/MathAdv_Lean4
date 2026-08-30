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

/-- **Rudin, Theorem 2.24 (special case of F-spaces: Banach spaces).**
If `X` is a complete normed space over `ℝ` and `Y` is a linear subspace of `X` whose
complement is of the first category (meagre), then `Y = X`.

The proof is by the Baire category theorem: if some `x ∉ Y`, then the coset `x + Y` is
contained in `Yᶜ`, hence meagre; translation is a homeomorphism, so `Y` itself is meagre,
and therefore `X = Y ∪ Yᶜ` would be meagre, contradicting Baire. -/
theorem rudin_2_24
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (Y : Submodule ℝ X)
  (h_complement_meager : IsMeagre ((Y : Set X)ᶜ)) :
  (Y : Set X) = Set.univ := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ (Y : Set X) := by
    by_contra! h
    exact hne (Set.eq_univ_of_forall h)
  -- `Y` is contained in the preimage of `Yᶜ` under the translation `z ↦ x + z`
  have hsub : (Y : Set X) ⊆ (fun z => x + z) ⁻¹' (Y : Set X)ᶜ := by
    intro y hy hmem
    exact hx (by simpa using Y.sub_mem hmem hy)
  have hYmeagre : IsMeagre (Y : Set X) :=
    IsMeagre.mono hsub
      (IsMeagre.preimage_of_isOpenMap (continuous_const.add continuous_id)
        (Homeomorph.addLeft x).isOpenMap h_complement_meager)
  have huniv : IsMeagre (Set.univ : Set X) := by
    have := hYmeagre.union h_complement_meager
    simpa using this
  exact not_isMeagre_of_isOpen isOpen_univ ⟨0, Set.mem_univ 0⟩ huniv
