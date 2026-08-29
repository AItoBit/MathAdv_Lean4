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
# Lovász, Exercise 19 (Combinatorial problems and exercises, 4.9)

Let `G` be a `(k-1)`-edge-connected, `k`-regular graph with an even number of vertices.
Remove `k-1` edges from `G`.  Then the remaining graph `G'` has a `1`-factor.

The tool used to solve the problem is **(d) Tutte's theorem**: a graph has a perfect
matching if and only if it has no *Tutte violator*, i.e. no vertex set `u` such that
deleting `u` leaves more than `|u|` odd components.
-/

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The neighbourhood of `v` in `G`, as a `Finset`. -/
def neighFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w)

/-- The degree of `v` in `G`. -/
def deg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (neighFinset G v).card

/-- `G` is `k`-regular. -/
def IsKRegular (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ v : V, deg G v = k

/-- `G'` is obtained from `G` by deleting exactly `m` edges, which are described by the
symmetric set `R` of ordered pairs. -/
def IsObtainedByRemovingExactlyMEdges (G G' : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ R : Finset (V × V),
    (∀ p ∈ R, p.1 ≠ p.2 ∧ G.Adj p.1 p.2) ∧
    (∀ p, p ∈ R → (p.2, p.1) ∈ R) ∧
    R.card / 2 = m ∧
    (∀ a b : V,
      G'.Adj a b ↔ G.Adj a b ∧ (a,b) ∉ R)

/-- `G` has a `1`-factor (a perfect matching), described by a fixed-point free involution
which matches every vertex to an adjacent one. -/
def HasOneFactor (G : SimpleGraph V) : Prop :=
  ∃ mate : V → V,
    Function.Involutive mate ∧
    (∀ v, mate v ≠ v) ∧
    (∀ v, G.Adj v (mate v))

/-- The ordered pairs `(a, b)` with `a ∈ S`, `b ∉ S` and `a` adjacent to `b`. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p =>
    G.Adj p.1 p.2 ∧ (p.1 ∈ S) ∧ (p.2 ∉ S))

/-- `G` is `c`-edge-connected (in the sense that every nontrivial cut has at least `c`
edges). -/
def EdgeConnectivityAtLeast (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) : Prop :=
  ∀ S : Finset V,
    S.Nonempty → S.card < Fintype.card V →
      c ≤ (cutEdges (V := V) G S).card

namespace Lovasz19

open Finset

/-! ### Counting ordered pairs of adjacent vertices -/

/-- Ordered pairs of adjacent vertices whose *first* entry lies in `C`. -/
def pairsFrom (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ C)

/-- Ordered pairs of adjacent vertices whose *second* entry lies in `C`. -/
def pairsTo (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.2 ∈ C)

/-- Ordered pairs of adjacent vertices with both entries in `C`. -/
def innerPairs (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ C ∧ p.2 ∈ C)

lemma card_pairsFrom (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (pairsFrom G C).card = ∑ v ∈ C, deg G v := by
  have h : pairsFrom G C = C.biUnion (fun v => (neighFinset G v).image (fun w => (v, w))) := by
    ext ⟨a, b⟩
    simp [pairsFrom, neighFinset]
    tauto
  rw [h, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun v _ => Finset.card_image_of_injective _ (fun x y hxy => by
      simpa using hxy)
  · intro x hx y hy hxy
    simp [Finset.disjoint_left]
    intro a ha b hb h1 h2
    exact hxy (by simp_all)

lemma card_pairsTo (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (pairsTo G C).card = ∑ v ∈ C, deg G v := by
  rw [← card_pairsFrom G C]
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro a ha; simp [pairsFrom, pairsTo] at ha ⊢; exact ⟨ha.1.symm, ha.2⟩
  · intro a _ b _ h; simp at h; exact Prod.ext h.2 h.1
  · intro b hb
    exact ⟨(b.2, b.1), by simp [pairsFrom, pairsTo] at hb ⊢; exact ⟨hb.1.symm, hb.2⟩, rfl⟩

lemma card_pairsTo_regular {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hreg : IsKRegular G k) (C : Finset V) : (pairsTo G C).card = k * C.card := by
  rw [card_pairsTo, Finset.sum_congr rfl (fun v _ => hreg v), Finset.sum_const, smul_eq_mul,
    mul_comm]

lemma even_card_innerPairs (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    Even (innerPairs G C).card := by
  have h : ((innerPairs G C).card : ZMod 2) = 0 := by
    have h0 : ∑ _p ∈ innerPairs G C, (1 : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro a _; decide
      · intro a ha _ hcon
        have h1 : a.2 = a.1 := congrArg Prod.fst hcon
        simp only [innerPairs, Finset.mem_filter] at ha
        have hadj := ha.2.1
        rw [h1] at hadj
        exact G.irrefl hadj
      · intro a ha
        simp only [innerPairs, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ⟨ha.1.symm, ha.2.2, ha.2.1⟩
      · intro a _; simp
    simpa using h0
  exact ZMod.natCast_eq_zero_iff_even.mp h

lemma card_cut_add_inner (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    (cutEdges G C).card + (innerPairs G C).card = ∑ v ∈ C, deg G v := by
  rw [← card_pairsFrom G C]
  have h1 : cutEdges G C = (pairsFrom G C).filter (fun p : V × V => p.2 ∉ C) := by
    ext p; simp [cutEdges, pairsFrom]; tauto
  have h2 : innerPairs G C = (pairsFrom G C).filter (fun p : V × V => p.2 ∈ C) := by
    ext p; simp [innerPairs, pairsFrom]; tauto
  rw [h1, h2, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- In a `k`-regular graph the cut determined by a set of *odd* cardinality has the same
parity as `k`. -/
lemma card_cut_parity {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hreg : IsKRegular G k) (C : Finset V) (hodd : Odd C.card) :
    (cutEdges G C).card % 2 = k % 2 := by
  obtain ⟨m, hm⟩ := even_card_innerPairs G C
  obtain ⟨t, ht⟩ := hodd
  have hsum : ∑ v ∈ C, deg G v = k * C.card := by
    rw [Finset.sum_congr rfl (fun v _ => hreg v), Finset.sum_const, smul_eq_mul, mul_comm]
  have hkc : k * C.card = 2 * (k * t) + k := by rw [ht]; ring
  have := card_cut_add_inner G C
  omega

/-! ### The counting heart of the argument -/

/-- The core counting argument. If `G` is `k`-regular and `(k-1)`-edge-connected, `G'` is
obtained from `G` by removing the edges in `R` with `|R| < 2k`, and `Q` is a family of at
least `|S| + 2` pairwise disjoint, nonempty, odd sets avoiding `S`, each of which is closed
under `G'`-adjacency outside `S`, then we get a contradiction. -/
lemma main_count
    {G G' : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (hreg : IsKRegular G k) (hconn : EdgeConnectivityAtLeast G (k - 1))
    {R : Finset (V × V)} (hR : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ (a, b) ∉ R)
    (hRcard : R.card < 2 * k)
    (S : Finset V) (Q : Finset (Finset V))
    (hne : ∀ C ∈ Q, C.Nonempty)
    (hodd : ∀ C ∈ Q, Odd C.card)
    (hdisj : ∀ C ∈ Q, ∀ D ∈ Q, C ≠ D → Disjoint C D)
    (hclosed : ∀ C ∈ Q, ∀ a ∈ C, ∀ b, b ∉ S → G'.Adj a b → b ∈ C)
    (hbig : S.card + 2 ≤ Q.card) : False := by
  classical
  set A : Finset V → Finset (V × V) := fun C => (cutEdges G C).filter (fun p => p.2 ∈ S) with hA
  set B : Finset V → Finset (V × V) := fun C => (cutEdges G C).filter (fun p => p.2 ∉ S) with hB
  -- every member of `Q` is a proper subset of the vertex set
  have hlt : ∀ C ∈ Q, C.card < Fintype.card V := by
    intro C hC
    have h2 : 1 < Q.card := by omega
    obtain ⟨X, hX, Y, hY, hXY⟩ := Finset.one_lt_card.mp h2
    have hex : ∃ D ∈ Q, D ≠ C := by
      rcases eq_or_ne X C with rfl | h
      · exact ⟨Y, hY, Ne.symm hXY⟩
      · exact ⟨X, hX, h⟩
    obtain ⟨D, hD, hDC⟩ := hex
    obtain ⟨v, hv⟩ := hne D hD
    have hvC : v ∉ C := Finset.disjoint_left.mp (hdisj D hD C hC hDC) hv
    calc C.card ≤ (Finset.univ.erase v).card := Finset.card_le_card (by
            intro x hx; simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            rintro rfl; exact hvC hx)
      _ < Fintype.card V := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
            have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
            simp only [Finset.card_univ]
            omega
  -- each cut has at least `k` edges
  have hcut : ∀ C ∈ Q, k ≤ (cutEdges G C).card := by
    intro C hC
    have h1 := hconn C (hne C hC) (hlt C hC)
    have h2 := card_cut_parity hreg C (hodd C hC)
    omega
  have hsplit : ∀ C : Finset V, (A C).card + (B C).card = (cutEdges G C).card := by
    intro C; exact Finset.card_filter_add_card_filter_not _
  have hAsub : ∀ C ∈ Q, A C ⊆ pairsTo G S := by
    intro C _ p hp
    simp only [hA, Finset.mem_filter, cutEdges, Finset.mem_univ, true_and] at hp
    simp only [pairsTo, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.1.1, hp.2⟩
  have hBsub : ∀ C ∈ Q, B C ⊆ R := by
    intro C hC p hp
    simp only [hB, Finset.mem_filter, cutEdges, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hadj, h1C, h2C⟩, h2S⟩ := hp
    by_contra hpR
    exact h2C (hclosed C hC p.1 h1C p.2 h2S ((hR p.1 p.2).mpr ⟨hadj, hpR⟩))
  have hdisjA : ∀ C ∈ Q, ∀ D ∈ Q, C ≠ D → Disjoint (A C) (A D) := by
    intro C hC D hD hCD
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [hA, Finset.mem_filter, cutEdges, Finset.mem_univ, true_and] at hp hq
    exact (Finset.disjoint_left.mp (hdisj C hC D hD hCD) hp.1.2.1) hq.1.2.1
  have hdisjB : ∀ C ∈ Q, ∀ D ∈ Q, C ≠ D → Disjoint (B C) (B D) := by
    intro C hC D hD hCD
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [hB, Finset.mem_filter, cutEdges, Finset.mem_univ, true_and] at hp hq
    exact (Finset.disjoint_left.mp (hdisj C hC D hD hCD) hp.1.2.1) hq.1.2.1
  have hsumA : ∑ C ∈ Q, (A C).card ≤ k * S.card := by
    rw [← Finset.card_biUnion hdisjA, ← card_pairsTo_regular hreg S]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hAsub)
  have hsumB : ∑ C ∈ Q, (B C).card ≤ R.card := by
    rw [← Finset.card_biUnion hdisjB]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hBsub)
  have hlow : k * Q.card ≤ ∑ C ∈ Q, (cutEdges G C).card := by
    calc k * Q.card = ∑ _C ∈ Q, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcut
  have hupper : ∑ C ∈ Q, (cutEdges G C).card = ∑ C ∈ Q, (A C).card + ∑ C ∈ Q, (B C).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ => (hsplit C).symm
  have hmul : k * (S.card + 2) ≤ k * Q.card := Nat.mul_le_mul_left k hbig
  have hexp : k * (S.card + 2) = k * S.card + 2 * k := by ring
  omega

/-! ### Components of `G - u` as finsets -/

/-- The vertex set of a connected component of `G - u`, as a `Finset` of `V`. -/
noncomputable def compFinset (G : SimpleGraph V) (u : Set V)
    (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => ∃ h : v ∈ ((⊤ : G.Subgraph).deleteVerts u).verts,
    ((⊤ : G.Subgraph).deleteVerts u).coe.connectedComponentMk ⟨v, h⟩ = c)

variable (G : SimpleGraph V) (u : Set V)

omit [DecidableEq V] in
lemma mem_compFinset_iff {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} {v : V} :
    v ∈ compFinset G u c ↔ ∃ h : v ∈ ((⊤ : G.Subgraph).deleteVerts u).verts,
      ((⊤ : G.Subgraph).deleteVerts u).coe.connectedComponentMk ⟨v, h⟩ = c := by
  simp [compFinset]

omit [DecidableEq V] in
lemma coe_compFinset (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) :
    (compFinset G u c : Set V) = Subtype.val '' c.supp := by
  ext v
  rw [Finset.mem_coe, mem_compFinset_iff, Set.mem_image]
  constructor
  · rintro ⟨h, hc⟩; exact ⟨⟨v, h⟩, hc, rfl⟩
  · rintro ⟨⟨w, hw⟩, hc, rfl⟩; exact ⟨hw, hc⟩

omit [DecidableEq V] in
lemma card_compFinset (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) :
    (compFinset G u c).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset, coe_compFinset, Set.ncard_image_of_injective _ Subtype.val_injective]

omit [DecidableEq V] in
lemma compFinset_nonempty (c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent) :
    (compFinset G u c).Nonempty := by
  refine ⟨c.out.1, ?_⟩
  rw [mem_compFinset_iff]
  exact ⟨c.out.2, c.out_eq⟩

omit [DecidableEq V] in
lemma compFinset_injective : Function.Injective (compFinset G u) := by
  intro c d h
  obtain ⟨v, hv⟩ := compFinset_nonempty G u c
  have hv' : v ∈ compFinset G u d := h ▸ hv
  rw [mem_compFinset_iff] at hv hv'
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h3, h4⟩ := hv'
  rw [← h2, ← h4]

omit [DecidableEq V] in
lemma compFinset_disjoint {c d : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent}
    (hcd : compFinset G u c ≠ compFinset G u d) :
    Disjoint (compFinset G u c) (compFinset G u d) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_compFinset_iff] at hv hv'
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h3, h4⟩ := hv'
  exact hcd (by rw [← h2, ← h4])

omit [DecidableEq V] in
lemma compFinset_notMem_u {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} {v : V}
    (hv : v ∈ compFinset G u c) : v ∉ u := by
  rw [mem_compFinset_iff] at hv
  obtain ⟨h, _⟩ := hv
  simpa using h.2

omit [DecidableEq V] in
lemma compFinset_closed {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent} {a b : V}
    (ha : a ∈ compFinset G u c) (hb : b ∉ u) (hab : G.Adj a b) : b ∈ compFinset G u c := by
  rw [mem_compFinset_iff] at ha ⊢
  obtain ⟨ha1, ha2⟩ := ha
  have hau : a ∉ u := by simpa using ha1.2
  have hb1 : b ∈ ((⊤ : G.Subgraph).deleteVerts u).verts := by simp [hb]
  refine ⟨hb1, ?_⟩
  rw [← ha2]
  symm
  apply SimpleGraph.ConnectedComponent.sound
  refine SimpleGraph.Adj.reachable ?_
  simp only [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj,
    SimpleGraph.Subgraph.top_adj]
  exact ⟨by simp, hau, by simp, hb, hab⟩

/-! ### From a perfect matching to a `1`-factor -/

omit [Fintype V] [DecidableEq V] in
lemma hasOneFactor_of_isPerfectMatching {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    HasOneFactor G := by
  classical
  have hex : ∀ v : V, ∃! w, M.Adj v w := fun v => hM.1 (hM.2 v)
  refine ⟨fun v => (hex v).choose, ?_, ?_, ?_⟩
  · intro v
    have h1 : M.Adj v (hex v).choose := (hex v).choose_spec.1
    exact ((hex ((hex v).choose)).choose_spec.2 v (M.adj_symm h1)).symm
  · intro v
    exact (M.adj_sub (hex v).choose_spec.1).ne'
  · intro v
    exact M.adj_sub (hex v).choose_spec.1

end Lovasz19

/-!
### The main theorem
-/

/-- **Lovász 4.9.19.**  A `k`-regular, `(k-1)`-edge-connected graph with an even number of
vertices keeps a `1`-factor after the removal of any `k-1` edges (`k ≥ 1`).

The proof uses **Tutte's theorem**, answer (d) of the multiple choice question. -/
theorem Lovasz_19
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k)
    (h_even : Even (Fintype.card V))
    (h_reg  : IsKRegular (V := V) G k)
    (h_edge : EdgeConnectivityAtLeast (V := V) G (k - 1))
    (G' : SimpleGraph V)
    (h_rem : IsObtainedByRemovingExactlyMEdges (V := V) G G' (k - 1)) :
    HasOneFactor (V := V) G' := by
  classical
  obtain ⟨R, -, -, hRcard, hR⟩ := h_rem
  have hRlt : R.card < 2 * k := by omega
  -- By Tutte's theorem it suffices to rule out Tutte violators.
  have hmatch : ∃ M : G'.Subgraph, M.IsPerfectMatching := by
    rw [SimpleGraph.tutte]
    intro u ht
    -- `ht` says that `u` is a Tutte violator; we derive a contradiction.
    rw [SimpleGraph.IsTutteViolator] at ht
    set T := ((⊤ : G'.Subgraph).deleteVerts u).coe with hT
    -- the family of odd components, viewed as finsets of `V`
    set Qc : Finset T.ConnectedComponent :=
      Finset.univ.filter (fun c => Odd c.supp.ncard) with hQc
    set Q : Finset (Finset V) := Qc.image (Lovasz19.compFinset G' u) with hQ
    have hQcard : Q.card = T.oddComponents.ncard := by
      rw [hQ, Finset.card_image_of_injective _ (Lovasz19.compFinset_injective G' u), hQc,
        Set.ncard_eq_toFinset_card']
      congr 1
      ext c
      simp [SimpleGraph.oddComponents]
    -- parity: the number of odd components has the same parity as `|V| - |u|`
    have hcardT : Nat.card ↥((⊤ : G'.Subgraph).deleteVerts u).verts
        = Fintype.card V - u.ncard := by
      have h : ((⊤ : G'.Subgraph).deleteVerts u).verts = Set.univ \ u := by simp
      rw [h, Nat.card_coe_set_eq, Set.ncard_sdiff (Set.subset_univ u), Set.ncard_univ,
        Nat.card_eq_fintype_card]
    have hpar : Odd T.oddComponents.ncard ↔ Odd (Fintype.card V - u.ncard) := by
      rw [SimpleGraph.odd_ncard_oddComponents, hcardT]
    have hule : u.ncard ≤ Fintype.card V := by
      have h := Set.ncard_le_ncard (Set.subset_univ u) (Set.finite_univ (α := V))
      simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h
    have hScard : (u.toFinset).card = u.ncard := by
      rw [Set.ncard_eq_toFinset_card']
    have hodd_iff : Odd (Fintype.card V - u.ncard) ↔ Odd u.ncard := by
      obtain ⟨m, hm⟩ := h_even
      omega
    -- hence a violation forces a gap of at least two
    have hbig : (u.toFinset).card + 2 ≤ Q.card := by
      rw [hScard, hQcard]
      have hpar' : Odd T.oddComponents.ncard ↔ Odd u.ncard := hpar.trans hodd_iff
      omega
    refine Lovasz19.main_count (G := G) (G' := G') hk h_reg h_edge hR hRlt u.toFinset Q
      ?_ ?_ ?_ ?_ hbig
    · rintro C hC
      rw [hQ, Finset.mem_image] at hC
      obtain ⟨c, -, rfl⟩ := hC
      exact Lovasz19.compFinset_nonempty G' u c
    · rintro C hC
      rw [hQ, Finset.mem_image] at hC
      obtain ⟨c, hc, rfl⟩ := hC
      rw [Lovasz19.card_compFinset]
      rw [hQc, Finset.mem_filter] at hc
      exact hc.2
    · rintro C hC D hD hCD
      rw [hQ, Finset.mem_image] at hC hD
      obtain ⟨c, -, rfl⟩ := hC
      obtain ⟨d, -, rfl⟩ := hD
      exact Lovasz19.compFinset_disjoint G' u hCD
    · rintro C hC a ha b hb hab
      rw [hQ, Finset.mem_image] at hC
      obtain ⟨c, -, rfl⟩ := hC
      rw [Set.mem_toFinset] at hb
      exact Lovasz19.compFinset_closed G' u ha hb hab
  obtain ⟨M, hM⟩ := hmatch
  exact Lovasz19.hasOneFactor_of_isPerfectMatching G' hM

/-- The hypothesis `1 ≤ k` cannot be dropped: for `k = 0` every hypothesis of the original
statement holds for the empty graph on two vertices, but it has no `1`-factor. -/
theorem Lovasz_19_k_zero_counterexample :
    Even (Fintype.card (Fin 2)) ∧
    IsKRegular (⊥ : SimpleGraph (Fin 2)) 0 ∧
    EdgeConnectivityAtLeast (⊥ : SimpleGraph (Fin 2)) (0 - 1) ∧
    IsObtainedByRemovingExactlyMEdges (⊥ : SimpleGraph (Fin 2)) ⊥ (0 - 1) ∧
    ¬ HasOneFactor (⊥ : SimpleGraph (Fin 2)) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro v; simp [deg, neighFinset]
  · intro S _ _; exact Nat.zero_le _
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  · rintro ⟨mate, -, -, h3⟩
    exact (h3 0).elim
