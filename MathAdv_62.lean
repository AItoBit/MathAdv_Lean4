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

/-- **Any finite simple graph with at least two vertices has two distinct vertices of the
same degree.**  (The relevant concept is the *pigeonhole principle*, answer (b): the `n`
degrees all lie in `{0, …, n-1}`, and the values `0` and `n-1` cannot both occur.) -/
theorem bona_11
    (α : Type*) [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (h₂ : 2 ≤ Fintype.card α) :
    ∃ u v : α, u ≠ v ∧ G.degree u = G.degree v := by
  by_contra hcon
  push_neg at hcon
  set n := Fintype.card α with hn
  -- If all degrees were distinct, the degree map into `Fin n` would be injective, ...
  have hinj : Function.Injective
      (fun x : α => (⟨G.degree x, G.degree_lt_card_verts x⟩ : Fin n)) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne (congrArg Fin.val hab)
  -- ... hence bijective, so some vertex has degree `0` and some vertex has degree `n - 1`.
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simpa using hn.symm⟩
  obtain ⟨u, hu⟩ := hbij.2 (⟨0, by omega⟩ : Fin n)
  obtain ⟨v, hv⟩ := hbij.2 (⟨n - 1, by omega⟩ : Fin n)
  have hu' : G.degree u = 0 := congrArg Fin.val hu
  have hv' : G.degree v = n - 1 := congrArg Fin.val hv
  -- A vertex of degree `n - 1` is adjacent to every other vertex.
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro x hx
    simp only [SimpleGraph.mem_neighborFinset] at hx
    exact Finset.mem_erase.2 ⟨fun h => G.irrefl (h ▸ hx), Finset.mem_univ x⟩
  have hcard : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp [SimpleGraph.card_neighborFinset_eq_degree, hv', hn]
  have heq : G.neighborFinset v = Finset.univ.erase v :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have huv : u ≠ v := by
    intro h
    rw [h, hv'] at hu'
    omega
  -- In particular `v` is adjacent to `u`, contradicting `G.degree u = 0`.
  have hadj : G.Adj v u := by
    have : u ∈ G.neighborFinset v := by
      rw [heq]; exact Finset.mem_erase.2 ⟨huv, Finset.mem_univ u⟩
    exact (SimpleGraph.mem_neighborFinset _ _ _).1 this
  have hmem : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj.symm
  have hpos := Finset.card_pos.2 ⟨v, hmem⟩
  rw [SimpleGraph.card_neighborFinset_eq_degree, hu'] at hpos
  omega

#print axioms bona_11
