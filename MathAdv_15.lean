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

/-- If `f : G →* H` is a surjective group homomorphism and `G` is cyclic, then `H` is cyclic. -/
theorem Gallian_16
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hG : IsCyclic G) :
    IsCyclic H := by
  obtain ⟨g, hg⟩ := hG
  refine ⟨⟨f g, ?_⟩⟩
  intro h
  obtain ⟨x, rfl⟩ := hf h
  obtain ⟨n, hn⟩ := hg x
  exact ⟨n, by rw [← hn]; simp⟩
