import Mathlib

/-!
# Minimal cross-cutting hypergraphs

A hypergraph on a vertex set `V` with edge set `E`, described by `vertsOf : E → Finset V`,
is *cross-cutting* if every nonempty proper subset `S` of the vertices is *crossed* by some
edge, i.e. some edge meets both `S` and its complement. It is *minimal* cross-cutting if no
single edge can be dropped while keeping the property.

We prove that a minimal cross-cutting hypergraph on `n` vertices has at most `n.choose (n/2)`
edges. In fact we prove the sharper bound `Fintype.card E ≤ n` : for each edge `e` minimality
produces a set `S e` crossed by `e` and by no other edge, and the indicator vectors of the sets
`S e` are linearly independent in `V → ℝ`. Since `n = n.choose 1 ≤ n.choose (n/2)`, the stated
bound follows.

Of the four classical results listed in the accompanying multiple-choice question, the one that
yields the stated bound `n.choose (n/2)` is (c) Sperner's theorem, whose extremal quantity is
exactly `n.choose (n/2)`.
-/

open Finset

/-- The hypergraph `vertsOf` is cross-cutting: every nonempty proper set of vertices is met
by some edge in both itself and its complement. -/
def CrossCutting {V E : Type*} [Fintype V] [DecidableEq V]
    (vertsOf : E → Finset V) : Prop :=
  ∀ S : Finset V,
    S.Nonempty → S ≠ Finset.univ →
    ∃ e : E,
      (vertsOf e ∩ S).Nonempty ∧ (vertsOf e ∩ (Finset.univ \ S)).Nonempty

/-- The hypergraph `vertsOf` is cross-cutting even after deleting the edge `e0`. -/
def CrossCuttingExcept {V E : Type*} [Fintype V] [DecidableEq V]
    (vertsOf : E → Finset V) (e0 : E) : Prop :=
  ∀ S : Finset V,
    S.Nonempty → S ≠ Finset.univ →
    ∃ e : E,
      e ≠ e0 ∧
      (vertsOf e ∩ S).Nonempty ∧ (vertsOf e ∩ (Finset.univ \ S)).Nonempty

/-- Minimality gives, for each edge `e0`, a vertex set crossed by `e0` and by no other edge. -/
lemma exists_private_cut {V E : Type*} [Fintype V] [DecidableEq V]
    (vertsOf : E → Finset V)
    (hCross : CrossCutting (V := V) (E := E) vertsOf)
    (hMinimal : ∀ e0 : E, ¬ CrossCuttingExcept (V := V) (E := E) vertsOf e0) (e0 : E) :
    ∃ S : Finset V,
      ((vertsOf e0 ∩ S).Nonempty ∧ (vertsOf e0 ∩ (Finset.univ \ S)).Nonempty) ∧
      ∀ e : E, e ≠ e0 →
        ¬ ((vertsOf e ∩ S).Nonempty ∧ (vertsOf e ∩ (Finset.univ \ S)).Nonempty) := by
  have h := hMinimal e0
  rw [CrossCuttingExcept] at h
  push Not at h
  obtain ⟨S, hne, hnu, hall⟩ := h
  refine ⟨S, ?_, ?_⟩
  · obtain ⟨e, he1, he2⟩ := hCross S hne hnu
    by_cases hee : e = e0
    · exact hee ▸ ⟨he1, he2⟩
    · exact absurd (hall e hee he1) (Finset.nonempty_iff_ne_empty.mp he2)
  · intro e he ⟨h1, h2⟩
    exact (Finset.nonempty_iff_ne_empty.mp h2) (hall e he h1)

/-- Sharper bound: a minimal cross-cutting hypergraph has at most as many edges as vertices.
The indicator vectors of the "private cuts" produced by minimality are linearly independent. -/
theorem minimal_crossCutting_card_edges_le_card_verts
    (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E]
    (vertsOf : E → Finset V)
    (hCross : CrossCutting (V := V) (E := E) vertsOf)
    (hMinimal : ∀ e0 : E, ¬ CrossCuttingExcept (V := V) (E := E) vertsOf e0) :
    Fintype.card E ≤ Fintype.card V := by
  classical
  choose S hS hS' using exists_private_cut vertsOf hCross hMinimal
  -- Indicator vectors of the private cuts.
  set g : E → (V → ℝ) := fun e v => if v ∈ S e then (1 : ℝ) else 0 with hg
  -- Key: if `e ≠ f` then the edge `f` does not cross `S e`, so `S e` is constant on `vertsOf f`.
  have hconst : ∀ e f : E, e ≠ f → ∀ u ∈ vertsOf f, ∀ w ∈ vertsOf f,
      (u ∈ S e ↔ w ∈ S e) := by
    intro e f hef u hu w hw
    have := hS' e f (Ne.symm hef)
    rw [not_and_or] at this
    rcases this with h | h
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      constructor
      · intro hu'
        exact absurd (Finset.mem_inter.2 ⟨hu, hu'⟩) (by simp [h])
      · intro hw'
        exact absurd (Finset.mem_inter.2 ⟨hw, hw'⟩) (by simp [h])
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      have key : ∀ x ∈ vertsOf f, x ∈ S e := by
        intro x hx
        by_contra hx'
        have : x ∈ vertsOf f ∩ (Finset.univ \ S e) :=
          Finset.mem_inter.2 ⟨hx, Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx'⟩⟩
        simp [h] at this
      exact ⟨fun _ => key w hw, fun _ => key u hu⟩
  have hli : LinearIndependent ℝ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc f
    obtain ⟨u, hu⟩ := (hS f).1
    obtain ⟨w, hw⟩ := (hS f).2
    rw [Finset.mem_inter] at hu hw
    obtain ⟨huf, huS⟩ := hu
    obtain ⟨hwf, hwS⟩ := hw
    rw [Finset.mem_sdiff] at hwS
    have hwS' : w ∉ S f := hwS.2
    have hcu : ∑ e : E, c e * (if u ∈ S e then (1 : ℝ) else 0) = 0 := by
      have := congrFun hc u
      simpa [hg, Finset.sum_apply] using this
    have hcw : ∑ e : E, c e * (if w ∈ S e then (1 : ℝ) else 0) = 0 := by
      have := congrFun hc w
      simpa [hg, Finset.sum_apply] using this
    have hsub : ∑ e : E, (c e * (if u ∈ S e then (1 : ℝ) else 0)
        - c e * (if w ∈ S e then (1 : ℝ) else 0)) = 0 := by
      rw [Finset.sum_sub_distrib, hcu, hcw, sub_zero]
    have hone : ∑ e : E, (c e * (if u ∈ S e then (1 : ℝ) else 0)
        - c e * (if w ∈ S e then (1 : ℝ) else 0)) = c f := by
      rw [Finset.sum_eq_single f]
      · simp [huS, hwS']
      · intro e _ hef
        have := hconst e f hef u huf w hwf
        by_cases h : u ∈ S e
        · simp [h, this.1 h]
        · have : w ∉ S e := fun hcon => h (this.2 hcon)
          simp [h, this]
      · intro h
        exact absurd (Finset.mem_univ f) h
    rw [hone] at hsub
    exact hsub
  have hcard : Fintype.card E ≤ Module.finrank ℝ (V → ℝ) := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at hcard

/-- A minimal cross-cutting hypergraph on `n` vertices has at most `n.choose (n / 2)` edges. -/
theorem Lovasz_23
    (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E]
    (vertsOf : E → Finset V)
    (n : ℕ) (hV : Fintype.card V = n)
    (hCross : CrossCutting (V := V) (E := E) vertsOf)
    (hMinimal : ∀ e0 : E, ¬ CrossCuttingExcept (V := V) (E := E) vertsOf e0) :
    Fintype.card E ≤ Nat.choose n (n / 2) := by
  have hcard := minimal_crossCutting_card_edges_le_card_verts V E vertsOf hCross hMinimal
  rw [hV] at hcard
  calc Fintype.card E ≤ n := hcard
    _ = Nat.choose n 1 := (Nat.choose_one_right n).symm
    _ ≤ Nat.choose n (n / 2) := Nat.choose_le_middle 1 n
