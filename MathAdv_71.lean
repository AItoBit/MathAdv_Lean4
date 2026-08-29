import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Covering the vertices of a graph by at most `α(G)` disjoint paths (Lovász, Problem 20)

We prove that the vertex set of a finite simple graph `G` can be covered by at most
`α(G)` vertex-disjoint paths, where `α(G)` is the independence number of `G`.

The multiple-choice companion question has answer **(d) Kőnig's theorem**.
-/

/-- The multiple choice answer. -/
def Lovasz_20_answer : String := "(d) Kőnig's theorem"

/-- A finite set of vertices is independent if no two distinct elements are adjacent. -/
def IsIndependentSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v

/-- The independence number of a finite graph. -/
noncomputable def IndependenceNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k}

/-- A sequence of vertices. -/
structure VPath (V : Type*) where
  seq : List V

/-- The set of vertices occurring on a vertex sequence. -/
def VPath.verts {V : Type*} (P : VPath V) : Set V :=
  {v | v ∈ P.seq}

/-- A vertex sequence is a path if it has no repetitions and consecutive vertices are adjacent. -/
def IsPath {V : Type*} (G : SimpleGraph V) (P : VPath V) : Prop :=
  P.seq.Nodup ∧ P.seq.IsChain G.Adj

namespace Lovasz20

variable {V : Type*} {G : SimpleGraph V}

/-- A nonempty vertex sequence, encoded as its first vertex together with the rest. -/
abbrev pth (p : V × List V) : List V := p.1 :: p.2

/-- Two nonempty vertex sequences are disjoint. -/
def Disj (p q : V × List V) : Prop := ∀ v, v ∈ pth p → v ∈ pth q → False

instance : Std.Symm (Disj (V := V)) where
  symm := fun _ _ h v hv hv' => h v hv' hv

/-- `L` is a cover of all vertices by pairwise disjoint paths of `G`. -/
def IsCover (G : SimpleGraph V) (L : List (V × List V)) : Prop :=
  (∀ p ∈ L, (pth p).Nodup ∧ (pth p).IsChain G.Adj) ∧
    L.Pairwise Disj ∧ (∀ v : V, ∃ p ∈ L, v ∈ pth p)

theorem IsCover.nodup {L : List (V × List V)} (hL : IsCover G L) : L.Nodup :=
  hL.2.1.imp (fun {x _} h => by rintro rfl; exact h x.1 (by simp) (by simp))

theorem IsCover.nodup_map_fst {L : List (V × List V)} (hL : IsCover G L) :
    (L.map Prod.fst).Nodup :=
  List.pairwise_map.2 (hL.2.1.imp (fun {x y} h he => h x.1 (by simp) (by simp [he])))

/-- The cover of `V` by singleton paths. -/
theorem exists_cover [Fintype V] (G : SimpleGraph V) :
    ∃ L : List (V × List V), IsCover G L := by
  refine ⟨(Finset.univ : Finset V).toList.map (fun v => (v, [])), ?_, ?_, ?_⟩
  · rintro p hp
    simp only [List.mem_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    exact ⟨List.nodup_singleton v, List.isChain_singleton v⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (Finset.nodup_toList (Finset.univ : Finset V))
    intro a b hab v hv hv'
    simp only [pth, List.mem_cons, List.not_mem_nil, or_false] at hv hv'
    exact hab (hv ▸ hv' ▸ rfl)
  · intro v
    exact ⟨(v, []), by simp, by simp⟩

/-- If two paths of a cover have adjacent first vertices, they can be joined, yielding a
strictly smaller cover. -/
theorem exists_smaller_cover [DecidableEq V] {L : List (V × List V)} (hL : IsCover G L)
    {p q : V × List V} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) (hadj : G.Adj p.1 q.1) :
    ∃ L' : List (V × List V), IsCover G L' ∧ L'.length < L.length := by
  obtain ⟨hpath, hdisj, hcov⟩ := hL
  have hLnodup : L.Nodup := IsCover.nodup ⟨hpath, hdisj, hcov⟩
  have hpqd : Disj p q := hdisj.forall hp hq hpq
  obtain ⟨a, t, hat⟩ : ∃ a t, (pth p).reverse ++ pth q = a :: t := by
    cases h : (pth p).reverse ++ pth q with
    | nil => simp [pth] at h
    | cons a t => exact ⟨a, t, rfl⟩
  have hpthat : pth (a, t) = (pth p).reverse ++ pth q := hat.symm
  have hqmem : q ∈ L.erase p := (List.mem_erase_of_ne (Ne.symm hpq)).2 hq
  refine ⟨(a, t) :: (L.erase p).erase q, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- every element is a path
    rintro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [hpthat]
      constructor
      · refine List.Nodup.append ?_ (hpath q hq).1 ?_
        · exact List.nodup_reverse.2 (hpath p hp).1
        · intro v hv hv'
          exact hpqd v (List.mem_reverse.1 hv) hv'
      · show List.IsChain G.Adj _
        rw [List.isChain_append]
        refine ⟨?_, (hpath q hq).2, ?_⟩
        · rw [List.isChain_reverse]
          exact List.IsChain.imp (fun _ _ => G.adj_symm) (hpath p hp).2
        · intro x hx y hy
          rw [List.getLast?_reverse] at hx
          simp only [pth, List.head?_cons, Option.mem_def, Option.some.injEq] at hx hy
          exact hx ▸ hy ▸ hadj
    · exact hpath r (List.mem_of_mem_erase (List.mem_of_mem_erase hr))
  · -- pairwise disjoint
    rw [List.pairwise_cons]
    refine ⟨?_, List.Pairwise.sublist ((List.erase_sublist).trans List.erase_sublist) hdisj⟩
    intro r hr v hv hv'
    have hrL : r ∈ L := List.mem_of_mem_erase (List.mem_of_mem_erase hr)
    have hrq : r ≠ q := ((List.Nodup.mem_erase_iff (hLnodup.erase p)).1 hr).1
    have hrp : r ≠ p :=
      ((List.Nodup.mem_erase_iff hLnodup).1 (List.mem_of_mem_erase hr)).1
    rw [hpthat, List.mem_append, List.mem_reverse] at hv
    rcases hv with hv | hv
    · exact (hdisj.forall hp hrL (Ne.symm hrp)) v hv hv'
    · exact (hdisj.forall hq hrL (Ne.symm hrq)) v hv hv'
  · -- covers all vertices
    intro v
    obtain ⟨r, hrL, hvr⟩ := hcov v
    by_cases hrp : r = p
    · exact ⟨(a, t), List.mem_cons_self, by
        rw [hpthat]; exact List.mem_append.2 (Or.inl (List.mem_reverse.2 (hrp ▸ hvr)))⟩
    · by_cases hrq : r = q
      · exact ⟨(a, t), List.mem_cons_self, by
          rw [hpthat]; exact List.mem_append.2 (Or.inr (hrq ▸ hvr))⟩
      · exact ⟨r, List.mem_cons_of_mem _
          ((List.mem_erase_of_ne hrq).2 ((List.mem_erase_of_ne hrp).2 hrL)), hvr⟩
  · -- the new cover is strictly smaller
    have h1 : (L.erase p).length = L.length - 1 := List.length_erase_of_mem hp
    have h2 : ((L.erase p).erase q).length = (L.erase p).length - 1 :=
      List.length_erase_of_mem hqmem
    have h3 : 0 < (L.erase p).length := List.length_pos_of_mem hqmem
    simp only [List.length_cons]
    omega

/-- From a cover of minimal size, the first vertices form an independent set. -/
theorem independent_of_minimal [DecidableEq V] {L : List (V × List V)} (hL : IsCover G L)
    (hmin : ∀ L' : List (V × List V), IsCover G L' → L.length ≤ L'.length) :
    IsIndependentSet G (L.map Prod.fst).toFinset := by
  intro u v hu hv huv hadj
  simp only [List.mem_toFinset, List.mem_map] at hu hv
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, rfl⟩ := hv
  have hpq : p ≠ q := by rintro rfl; exact huv rfl
  obtain ⟨L', hL', hlt⟩ := exists_smaller_cover hL hp hq hpq hadj
  exact absurd (hmin L' hL') (by omega)

end Lovasz20

open Lovasz20 in
/-- **Gallai–Milgram theorem for undirected graphs (Lovász, Problem 20).**
The vertices of a finite graph `G` can be covered by at most `α(G)` vertex-disjoint paths. -/
theorem Lovasz_20
    {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    ∃ m : ℕ, m ≤ IndependenceNumber G ∧
      ∃ P : Fin m → VPath V,
        (∀ i, IsPath G (P i)) ∧
        (∀ i j, i ≠ j → ((P i).verts ∩ (P j).verts = (∅ : Set V))) ∧
        (∀ v : V, ∃ i : Fin m, v ∈ (P i).verts) := by
  -- choose a cover with the minimal number of paths
  have hne : ∃ n : ℕ, ∃ L : List (V × List V), IsCover G L ∧ L.length = n := by
    obtain ⟨L, hL⟩ := exists_cover G
    exact ⟨L.length, L, hL, rfl⟩
  classical
  obtain ⟨L, hL, hlen⟩ := Nat.find_spec hne
  have hmin : ∀ L' : List (V × List V), IsCover G L' → L.length ≤ L'.length := by
    intro L' hL'
    have : Nat.find hne ≤ L'.length := Nat.find_le ⟨L', hL', rfl⟩
    omega
  refine ⟨L.length, ?_, fun i => ⟨pth (L.get i)⟩, ?_, ?_, ?_⟩
  · -- the first vertices form an independent set of size `L.length`
    have hind : IsIndependentSet G (L.map Prod.fst).toFinset := independent_of_minimal hL hmin
    have hcard : (L.map Prod.fst).toFinset.card = L.length := by
      rw [List.toFinset_card_of_nodup hL.nodup_map_fst, List.length_map]
    have hmem : L.length ∈ {k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k} :=
      ⟨_, hind, hcard⟩
    refine le_csSup ?_ hmem
    refine ⟨Fintype.card V, ?_⟩
    rintro k ⟨S, -, rfl⟩
    exact S.card_le_univ.trans_eq (Finset.card_univ)
  · intro i
    exact hL.1 _ (List.get_mem L i)
  · intro i j hij
    ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hvi hvj
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have := List.pairwise_iff_get.1 hL.2.1
    rcases lt_or_gt_of_ne hij' with h | h
    · exact this ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩ h v hvi hvj
    · exact this ⟨j.val, j.isLt⟩ ⟨i.val, i.isLt⟩ h v hvj hvi
  · intro v
    obtain ⟨p, hp, hvp⟩ := hL.2.2 v
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hp
    refine ⟨i, ?_⟩
    show v ∈ pth (L.get i)
    rw [hi]
    exact hvp
