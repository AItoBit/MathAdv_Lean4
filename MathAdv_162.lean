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
# No submersion from a nonempty compact manifold to `ℝ^k` (`k > 0`)

Reasoning (a): a smooth submersion is an open map, so its image would be a nonempty
open *and* compact — hence closed — subset of the connected space `ℝ^k`, forcing the
image to be all of `ℝ^k`; but `ℝ^k` is not compact for `k > 0`.

The statement below isolates the purely topological core of the argument: there is no
continuous open map from a nonempty compact space to `ℝ^k` when `k > 0`.
-/
theorem Lee_4_6_core
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [Nonempty M] :
    ∀ k : ℕ, 0 < k → ¬ ∃ F : M → (Fin k → ℝ), Continuous F ∧ IsOpenMap F := by
  rintro k hk ⟨F, hcont, hopen⟩
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hcpt : IsCompact (Set.range F) := isCompact_range hcont
  have hclopen : IsClopen (Set.range F) := ⟨hcpt.isClosed, hopen.isOpen_range⟩
  have huniv : Set.range F = Set.univ := hclopen.eq_univ (Set.range_nonempty F)
  have hcs : CompactSpace (Fin k → ℝ) := ⟨by rw [← huniv]; exact hcpt⟩
  exact absurd hcs (not_compactSpace_iff.mpr inferInstance)
