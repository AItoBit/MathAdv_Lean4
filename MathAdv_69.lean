import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Lovász, Problem 18: Menger's Theorem for (A, B)-paths

Let `A, B` be disjoint subsets of `V(G)` such that every set `X` meeting all
`(A, B)`-paths contains at least `k` vertices. Then there are `k` pairwise
vertex-disjoint `(A, B)`-paths.

The tool used to solve this problem is **(b) Menger's theorem**.
-/

/-- The multiple choice answer. -/
def Lovasz_18_answer : String := "(b) Menger's theorem"

/-- **Menger's Theorem for $(A, B)$-paths (Lovász, Problem 18).**

Let `G` be a simple graph, and `A, B` disjoint sets of vertices. If every vertex set `X`
that intersects all `(A, B)`-paths has cardinality at least `k` (formalized via an injective
map `Fin k → V` landing in `X`), then there exist `k` pairwise vertex-disjoint `(A, B)`-paths. -/
theorem Lovasz_18
    {V : Type*} (G : SimpleGraph V) (A B : Set V) (hAB : A ∩ B = (∅ : Set V)) (k : ℕ)
    (Path : Type*) (verts : Path → Set V) (isAB : Path → Prop)
    (h : ∀ X : Set V,
          (∀ P : Path, isAB P → (X ∩ verts P).Nonempty) →
          ∃ f : Fin k → V, (∀ i, f i ∈ X) ∧ Function.Injective f) :
    ∃ P : Fin k → Path,
      (∀ i, isAB (P i)) ∧
      (∀ i j, i ≠ j → ((verts (P i)) ∩ (verts (P j)) = (∅ : Set V))) := by
  sorry
