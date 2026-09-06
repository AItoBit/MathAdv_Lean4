/-
Lovasz 18 / combinatorial_4_9: the A-B version of Menger's theorem.

-/
import Mathlib

open Function

/-! ## Part 1: the statement as given is false -/

/-- The dataset statement, universe-instantiated at `Type`. -/
def MengerAsStated : Prop :=
  ∀ (V : Type) (_G : SimpleGraph V) (A B : Set V), A ∩ B = (∅ : Set V) → ∀ (k : ℕ)
    (Path : Type) (verts : Path → Set V) (isAB : Path → Prop),
    (∀ X : Set V,
        (∀ P : Path, isAB P → (X ∩ verts P).Nonempty) →
        ∃ f : Fin k → V, (∀ i, f i ∈ X) ∧ Injective f) →
    ∃ P : Fin k → Path,
      (∀ i, isAB (P i)) ∧
      (∀ i j, i ≠ j → (verts (P i) ∩ verts (P j) = (∅ : Set V)))

/-- The triangle hypergraph: three "paths" on three vertices, `V3 i` being
everything other than `i`. Any two of them meet, but no single vertex meets
all three. -/
private def V3 : Fin 3 → Set (Fin 3) := fun i => {x | x ≠ i}

private lemma exists_ne_ne : ∀ i j : Fin 3, ∃ x : Fin 3, x ≠ i ∧ x ≠ j := by decide

/-- Every set meeting all three of `V3 0, V3 1, V3 2` has at least two elements:
pick `a` in it, then `V3 a` supplies a second element different from `a`. -/
private lemma triangle_cut_large (X : Set (Fin 3))
    (hX : ∀ P : Fin 3, True → (X ∩ V3 P).Nonempty) :
    ∃ f : Fin 2 → Fin 3, (∀ i, f i ∈ X) ∧ Injective f := by
  obtain ⟨a, haX, -⟩ := hX 0 trivial
  obtain ⟨b, hbX, hba⟩ := hX a trivial
  simp only [V3, Set.mem_ofPred_eq] at hba
  have hab : a ≠ b := fun h => hba h.symm
  refine ⟨![a, b], ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using haX
    · simpa using hbX
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem mengerAsStated_false : ¬ MengerAsStated := by
  intro H
  obtain ⟨P, -, hdisj⟩ :=
    H (Fin 3) (⊥ : SimpleGraph (Fin 3)) ∅ ∅ (by simp) 2 (Fin 3) V3 (fun _ => True)
      triangle_cut_large
  obtain ⟨x, hx0, hx1⟩ := exists_ne_ne (P 0) (P 1)
  have hmem : x ∈ V3 (P 0) ∩ V3 (P 1) := ⟨hx0, hx1⟩
  rw [hdisj 0 1 (by decide)] at hmem
  simpa using hmem


/-! ## Part 2: a statement that actually says Menger

The fix is to make paths be paths *of `G`*, running from `A` to `B`. -/

/-- A path in `G` starting in `A` and ending in `B`. -/
structure ABPath {V : Type*} (G : SimpleGraph V) (A B : Set V) where
  fst : V
  snd : V
  walk : G.Walk fst snd
  isPath : walk.IsPath
  fst_mem : fst ∈ A
  snd_mem : snd ∈ B

namespace ABPath

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- The vertices visited by the path. -/
def verts (p : ABPath G A B) : Set V := {x | x ∈ p.walk.support}

end ABPath

/-- Menger, vertex version, `A`-`B` form: if every set of vertices meeting all
`A`-`B` paths has at least `k` elements, there are `k` pairwise disjoint
`A`-`B` paths. -/
def MengerAB : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (A B : Set V) (k : ℕ),
    (∀ X : Set V,
        (∀ p : ABPath G A B, (X ∩ p.verts).Nonempty) →
        ∃ f : Fin k → V, (∀ i, f i ∈ X) ∧ Injective f) →
    ∃ p : Fin k → ABPath G A B,
      ∀ i j, i ≠ j → (p i).verts ∩ (p j).verts = (∅ : Set V)

/-
Note: `A ∩ B = ∅` is not needed and is in fact the wrong hypothesis — the
standard A-B Menger allows A and B to meet, and a vertex of `A ∩ B` is a
one-vertex A-B path. The dataset carried `hAB` over from a different phrasing.
-/
