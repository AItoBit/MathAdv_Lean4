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
# Two-colouring the vertices of a simple planar map

Lovász, Problem 21 (combinatorial 4.9):
*Prove that we can two-colour the points of every simple planar map `G` in such a way that
each face receives both colours.*

The multiple-choice companion question ("which tool can be used to solve this problem?")
has answer **(c) Sperner's lemma**.

This file contains:

* the user-provided abstraction `SimplePlanarMap` and the statement `Lovasz_21`;
* a proof that `Lovasz_21`, **as stated**, is false: the only hypothesis it records about a
  planar map is that every face carries two distinct vertices, and that is far too weak
  (an odd "cycle" of two-element faces is a counterexample). The original statement is
  therefore kept, commented out, together with `Lovasz_21_is_false`;
* a corrected statement `Lovasz_21_corrected`, which adds the two properties of a *simple
  planar* map that the classical argument actually uses: the map can be refined to a
  triangulation, so every face contains three mutually adjacent vertices, and a planar
  graph admits a proper colouring with four colours. Merging the four colours in pairs
  then gives the required two-colouring.
-/

structure SimplePlanarMap {V : Type*} (G : SimpleGraph V)
    (Faces : Type*) (vertsOnFace : Faces → Set V) : Prop where
  face_nontrivial : ∀ f : Faces, ∃ v w : V,
    v ∈ vertsOnFace f ∧ w ∈ vertsOnFace f ∧ v ≠ w

/-- Answer to the multiple-choice question: (c), Sperner's lemma. -/
def Lovasz_21_multiple_choice_answer : Char := 'c'

/-
The original statement. It is false; see `Lovasz_21_is_false` below.

theorem Lovasz_21
    {V : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (Faces : Type*) (vertsOnFace : Faces → Set V)
    (hmap : SimplePlanarMap G Faces vertsOnFace) :
    ∃ c : V → Bool,
      ∀ f : Faces, ∃ v w : V,
        v ∈ vertsOnFace f ∧ w ∈ vertsOnFace f ∧ c v ≠ c w := by
  sorry
-/

/-- The counterexample data: three "vertices" `Fin 3`, and three "faces", the face `i`
consisting of the two vertices `i` and `i + 1`. -/
def counterFaces (i : Fin 3) : Set (Fin 3) := {i, i + 1}

lemma counterFaces_isMap :
    SimplePlanarMap (⊤ : SimpleGraph (Fin 3)) (Fin 3) counterFaces := by
  refine ⟨fun i => ⟨i, i + 1, ?_, ?_, ?_⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · revert i; decide

lemma counterFaces_not_two_colourable :
    ¬ ∃ c : Fin 3 → Bool, ∀ f : Fin 3, ∃ v w : Fin 3,
        v ∈ counterFaces f ∧ w ∈ counterFaces f ∧ c v ≠ c w := by
  rintro ⟨c, hc⟩
  have h : ∀ i : Fin 3, c i ≠ c (i + 1) := by
    intro i
    obtain ⟨v, w, hv, hw, hvw⟩ := hc i
    simp only [counterFaces, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
      first
        | exact absurd rfl hvw
        | exact hvw
        | exact hvw.symm
  have h0 : c 0 ≠ c 1 := h 0
  have h1 : c 1 ≠ c 2 := h 1
  have h2 : c 2 ≠ c 0 := h 2
  rcases Bool.eq_false_or_eq_true (c 0) with a | a <;>
    rcases Bool.eq_false_or_eq_true (c 1) with b | b <;>
      rcases Bool.eq_false_or_eq_true (c 2) with d | d <;>
        simp_all

/-- The statement `Lovasz_21` is false as it stands: knowing only that every face carries two
distinct vertices does not suffice to two-colour the vertices so that no face is
monochromatic. -/
theorem Lovasz_21_is_false :
    ¬ (∀ (V : Type) (G : SimpleGraph V) (_ : DecidableEq V) (_ : DecidableRel G.Adj)
        (Faces : Type) (vertsOnFace : Faces → Set V),
        SimplePlanarMap G Faces vertsOnFace →
        ∃ c : V → Bool,
          ∀ f : Faces, ∃ v w : V,
            v ∈ vertsOnFace f ∧ w ∈ vertsOnFace f ∧ c v ≠ c w) := by
  intro h
  exact counterFaces_not_two_colourable
    (h (Fin 3) ⊤ inferInstance inferInstance (Fin 3) counterFaces counterFaces_isMap)

/-! ### A corrected statement

The classical solution of the problem uses two genuine features of a *simple planar* map,
neither of which is recorded in `SimplePlanarMap`:

* each face of a simple planar map is bounded by a cycle of length at least `3`, and inserting
  diagonals triangulates it; hence every face contains three mutually adjacent vertices;
* a planar graph can be properly coloured with four colours.

Merging the four colours into two pairs then works: the three vertices of a triangle get three
distinct colours out of four, so they cannot all land in the same pair. -/

/-- The hypotheses on a map that the argument actually needs. -/
structure TriangulatedFourColourableMap {V : Type*} (G : SimpleGraph V)
    (Faces : Type*) (vertsOnFace : Faces → Set V) : Prop where
  /-- Every face contains three mutually adjacent vertices (triangulate the face). -/
  face_triangle : ∀ f : Faces, ∃ u v w : V,
    u ∈ vertsOnFace f ∧ v ∈ vertsOnFace f ∧ w ∈ vertsOnFace f ∧
      G.Adj u v ∧ G.Adj v w ∧ G.Adj u w
  /-- The graph has a proper colouring with four colours (four colour theorem). -/
  four_colourable : ∃ q : V → Fin 4, ∀ ⦃u v : V⦄, G.Adj u v → q u ≠ q v

/-- Three distinct elements of `Fin 4` cannot all lie in the same half `{0,1}` or `{2,3}`. -/
lemma fin_four_not_all_same_half (a b c : Fin 4) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬ (decide (a.val < 2) = decide (b.val < 2) ∧ decide (b.val < 2) = decide (c.val < 2)) := by
  revert hab hbc hac
  revert a b c
  decide

/-- **Corrected form of `Lovasz_21`.** If every face of the map contains a triangle of `G`
(which holds for a simple planar map, after triangulating its faces) and `G` is properly
`4`-colourable (which holds for planar graphs), then the vertices can be two-coloured so that
every face receives both colours. -/
theorem Lovasz_21_corrected
    {V : Type*} (G : SimpleGraph V)
    (Faces : Type*) (vertsOnFace : Faces → Set V)
    (hmap : TriangulatedFourColourableMap G Faces vertsOnFace) :
    ∃ c : V → Bool,
      ∀ f : Faces, ∃ v w : V,
        v ∈ vertsOnFace f ∧ w ∈ vertsOnFace f ∧ c v ≠ c w := by
  obtain ⟨q, hq⟩ := hmap.four_colourable
  refine ⟨fun x => decide ((q x).val < 2), fun f => ?_⟩
  obtain ⟨u, v, w, hu, hv, hw, huv, hvw, huw⟩ := hmap.face_triangle f
  by_contra hcon
  push Not at hcon
  exact fin_four_not_all_same_half (q u) (q v) (q w) (hq huv) (hq hvw) (hq huw)
    ⟨hcon u v hu hv, hcon v w hv hw⟩
