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

/-!
# Lovász 17 (Whitney duality) — analysis of the proposed formalization

The informal statement is Whitney's theorem: *a connected graph `G` is planar iff there is a
graph `G*` and a bijection `φ : E(G) → E(G*)` carrying complements of spanning trees of `G`
to spanning trees of `G*` and conversely.*

The multiple-choice question attached to the problem asks which tool can be used to solve it;
the answer is **(a) MacLane's criterion**, recorded formally as `Lovasz_17_mcq_answer` below.

This file records two facts about the proposed Lean statement (reproduced verbatim, commented
out, as `Lovasz_17` at the end of the file):

* `Lovasz_17_abstract_predicates_false`: as stated, `Connected`, `Planar` and `IsSpanningTreeOn`
  are *arbitrary* predicates supplied as hypotheses, with no defining axioms. Consequently the
  statement is not a theorem: it is refuted by instantiating `Planar` with the always-false
  predicate and `IsSpanningTreeOn` with the always-true predicate.

* `Lovasz_17_false_for_planar_K2`: even after replacing the abstract predicates by their genuine
  meanings (`SimpleGraph.Connected`, and `IsSpanningTreeSet` below for spanning trees), the
  statement is still false, for a reason intrinsic to `SimpleGraph`: the dual of a planar graph is
  in general a *multigraph*. Already for `K₂` (connected and planar) no simple graph `G*` can
  work, because the dual of `K₂` is a single vertex with a loop. This is `K2_has_no_dual`, a
  special case of `tree_has_no_dual`: no tree with at least one edge has a simple-graph dual.
-/

/-- The type of edges of a graph, as in the problem statement. -/
def EdgeType {V : Type*} (G : SimpleGraph V) : Type _ :=
  { e : Sym2 V // e ∈ G.edgeSet }

/-- A set `S` of edges of `G` is a *spanning tree* of `G` when the spanning subgraph of `G`
whose edge set is `S` is a tree (i.e. connected and acyclic on the full vertex set of `G`). -/
def IsSpanningTreeSet {V : Type*} (G : SimpleGraph V) (S : Set (EdgeType G)) : Prop :=
  (SimpleGraph.fromEdgeSet (Subtype.val '' S)).IsTree

/-! ## Basic facts -/

/-- `K₂` is a tree. -/
theorem topBool_isTree : (⊤ : SimpleGraph Bool).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.connected_top, ?_⟩
  simp only [Nat.card_eq_fintype_card, SimpleGraph.edgeSet_top,
    Fintype.card_subtype, Fintype.card_bool]
  decide

/-- The full edge set of a tree is a spanning tree of it. -/
theorem univ_isSpanningTreeSet_of_isTree {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) :
    IsSpanningTreeSet G Set.univ := by
  unfold IsSpanningTreeSet
  have h_img : Subtype.val '' (Set.univ : Set (EdgeType G)) = G.edgeSet := by
    ext e
    simp [EdgeType]
  rw [h_img, SimpleGraph.fromEdgeSet_edgeSet]
  exact hG

/-- If the empty edge set is a spanning tree of a graph, the graph has a single vertex. -/
theorem subsingleton_of_empty_isSpanningTree {W : Type*} {H : SimpleGraph W}
    (h : IsSpanningTreeSet H (∅ : Set (EdgeType H))) : Subsingleton W := by
  unfold IsSpanningTreeSet at h
  have h_img : Subtype.val '' (∅ : Set (EdgeType H)) = ∅ := Set.image_empty _
  rw [h_img, SimpleGraph.fromEdgeSet_empty] at h
  exact ⟨fun a b => SimpleGraph.reachable_bot.mp (h.isConnected.preconnected a b)⟩

/-- A graph on a subsingleton vertex type has no edges. -/
theorem edgeType_isEmpty_of_subsingleton {W : Type*} [Subsingleton W] (H : SimpleGraph W) :
    IsEmpty (EdgeType H) := by
  constructor
  rintro ⟨e, he⟩
  induction e with
  | _ a b => exact ((H.mem_edgeSet).mp he).ne (Subsingleton.elim a b)

/-! ## A tree with an edge has no simple-graph dual -/

/-- **No tree with at least one edge admits a dual in the sense of the problem statement.**
A tree `G` is connected and planar, yet there is no simple graph `G*` together with a bijection of
edge sets sending complements of spanning trees of `G` to spanning trees of `G*`: the whole edge
set of `G` is a spanning tree, its complement is empty, so `G*` would have to have exactly one
vertex, hence no edges at all — contradicting the bijection with the nonempty edge set of `G`. -/
theorem tree_has_no_dual {V : Type} {G : SimpleGraph V} (hG : G.IsTree) (e : EdgeType G) :
    ¬ ∃ (Vstar : Type) (Gstar : SimpleGraph Vstar) (phi : EdgeType G ≃ EdgeType Gstar),
        ∀ (T : Set (EdgeType G)),
          IsSpanningTreeSet G T →
          IsSpanningTreeSet Gstar (Set.image phi (Set.univ \ T)) := by
  rintro ⟨Vstar, Gstar, phi, h⟩
  have h0 := h Set.univ (univ_isSpanningTreeSet_of_isTree hG)
  simp only [Set.sdiff_self, Set.image_empty] at h0
  have : Subsingleton Vstar := subsingleton_of_empty_isSpanningTree h0
  exact (edgeType_isEmpty_of_subsingleton Gstar).elim (phi e)

/-- Specialization to `K₂`: the connected planar graph `K₂` has no simple-graph dual. -/
theorem K2_has_no_dual :
    ¬ ∃ (Vstar : Type) (Gstar : SimpleGraph Vstar)
        (phi : EdgeType (⊤ : SimpleGraph Bool) ≃ EdgeType Gstar),
        ∀ (T : Set (EdgeType (⊤ : SimpleGraph Bool))),
          IsSpanningTreeSet (⊤ : SimpleGraph Bool) T →
          IsSpanningTreeSet Gstar (Set.image phi (Set.univ \ T)) :=
  tree_has_no_dual topBool_isTree ⟨s(true, false), by simp⟩

/-- With the genuine notions of connectedness and spanning tree, the proposed equivalence fails
for `K₂` under *any* notion of planarity that (correctly) declares `K₂` planar. -/
theorem Lovasz_17_false_for_planar_K2
    (Planar : SimpleGraph Bool → Prop) (hplanar : Planar ⊤) :
    ¬ (Planar ⊤ ↔
      ∃ (Vstar : Type) (Gstar : SimpleGraph Vstar)
        (phi : EdgeType (⊤ : SimpleGraph Bool) ≃ EdgeType Gstar),
          (∀ (T : Set (EdgeType (⊤ : SimpleGraph Bool))),
              IsSpanningTreeSet (⊤ : SimpleGraph Bool) T →
              IsSpanningTreeSet Gstar (Set.image phi (Set.univ \ T))) ∧
          (∀ (Tstar : Set (EdgeType Gstar)),
              IsSpanningTreeSet Gstar Tstar →
              IsSpanningTreeSet (⊤ : SimpleGraph Bool)
                (Set.image phi.symm (Set.univ \ Tstar)))) := by
  intro hiff
  obtain ⟨Vstar, Gstar, phi, h1, _⟩ := hiff.mp hplanar
  exact K2_has_no_dual ⟨Vstar, Gstar, phi, h1⟩

/-- `K₂` really is connected, so the counterexample above satisfies the hypothesis of the
original statement. -/
theorem K2_connected : (⊤ : SimpleGraph Bool).Connected := SimpleGraph.connected_top

/-! ## The statement with abstract predicates is refutable -/

/-- **The proposed statement, read literally, is false.** In it `Connected`, `Planar` and
`IsSpanningTreeOn` are unconstrained predicate parameters, so nothing ties them to their intended
meanings. Taking `Planar` to be always false, `Connected` always true and `IsSpanningTreeOn`
always true refutes the universally quantified statement. -/
theorem Lovasz_17_abstract_predicates_false :
    ¬ ∀ (V : Type) (G : SimpleGraph V) (Connected : SimpleGraph V → Prop)
        (Planar : SimpleGraph V → Prop),
        Connected G →
        ∀ (IsSpanningTreeOn : ∀ {W : Type} (H : SimpleGraph W), Set (EdgeType H) → Prop),
          (Planar G ↔
            ∃ (Vstar : Type) (Gstar : SimpleGraph Vstar)
              (phi : EdgeType G ≃ EdgeType Gstar),
                (∀ (T : Set (EdgeType G)),
                    IsSpanningTreeOn G T →
                    IsSpanningTreeOn Gstar (Set.image phi (Set.univ \ T))) ∧
                (∀ (Tstar : Set (EdgeType Gstar)),
                    IsSpanningTreeOn Gstar Tstar →
                    IsSpanningTreeOn G (Set.image phi.symm (Set.univ \ Tstar)))) := by
  intro h
  have hiff := h Bool ⊤ (fun _ => True) (fun _ => False) trivial (fun _ _ => True)
  exact hiff.mpr ⟨Bool, ⊤, Equiv.refl _, fun _ _ => trivial, fun _ _ => trivial⟩

/-! ## The multiple-choice question -/

/-- The four offered options. -/
inductive Lovasz17Option
  | MacLaneCriterion
  | MengerTheorem
  | SpernerLemma
  | TutteTheorem
  deriving DecidableEq, Repr

/-- The answer to the multiple-choice question is (a), MacLane's criterion. -/
def Lovasz_17_mcq_answer : Lovasz17Option := Lovasz17Option.MacLaneCriterion
