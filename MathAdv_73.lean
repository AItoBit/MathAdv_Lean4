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

/-! # Dirac's theorem for `r`-regular graphs on `2n+1` vertices

An `r`-regular simple graph on `2n+1` vertices with `r ≥ n+1` has a Hamiltonian circuit.
This is an instance of Dirac's theorem (minimum degree at least half the number of vertices).
-/

def neighFinset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w)

def gdeg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (neighFinset G v).card

def IsRegularR {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : Prop :=
  ∀ v : V, gdeg G v = r

def HasHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ cyc : List V,
    cyc.Nodup ∧
    cyc.length = Fintype.card V ∧
    (∀ v : V, v ∈ cyc) ∧
    cyc.IsChain G.Adj ∧
    match cyc with
    | [] => False
    | a :: _ =>
        match cyc.getLast? with
        | none => False
        | some l => G.Adj l a

namespace Dirac

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma mem_neighFinset {v w : V} : w ∈ neighFinset G v ↔ G.Adj v w := by
  simp [neighFinset]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- There is a path (nodup list which is a chain for adjacency) of maximum length. -/
lemma exists_max_path :
    ∃ L : List V, L.Nodup ∧ List.IsChain G.Adj L ∧
      ∀ M : List V, M.Nodup → List.IsChain G.Adj M → M.length ≤ L.length := by
  classical
  set s : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
    (fun m => ∃ M : List V, M.Nodup ∧ List.IsChain G.Adj M ∧ M.length = m) with hs
  have hmem : ∀ M : List V, M.Nodup → List.IsChain G.Adj M → M.length ∈ s := by
    intro M h1 h2
    have : M.length ≤ Fintype.card V := h1.length_le_card
    simp only [hs, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨M, h1, h2, rfl⟩⟩
  have hne : s.Nonempty := ⟨0, by simpa using hmem [] (by simp) List.IsChain.nil⟩
  obtain ⟨m, hms, hmge⟩ : ∃ m ∈ s, ∀ k ∈ s, k ≤ m := ⟨s.max' hne, s.max'_mem hne, fun k hk => s.le_max' k hk⟩
  simp only [hs, Finset.mem_filter, Finset.mem_range] at hms
  obtain ⟨-, L, h1, h2, h3⟩ := hms
  exact ⟨L, h1, h2, fun M hM1 hM2 => h3 ▸ hmge _ (hmem M hM1 hM2)⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A maximum path contains all neighbours of its head. -/
lemma head_neighbors_mem {L : List V} (hnd : L.Nodup) (hch : List.IsChain G.Adj L)
    (hmax : ∀ M : List V, M.Nodup → List.IsChain G.Adj M → M.length ≤ L.length)
    {a : V} (ha : L.head? = some a) {w : V} (hw : G.Adj a w) : w ∈ L := by
  by_contra hmem
  have hM : (w :: L).Nodup := List.nodup_cons.mpr ⟨hmem, hnd⟩
  have hC : List.IsChain G.Adj (w :: L) := by
    rw [List.isChain_cons]
    refine ⟨fun y hy => ?_, hch⟩
    rw [ha] at hy
    cases hy
    exact hw.symm
  have := hmax _ hM hC
  simp at this

omit [Fintype V] [DecidableRel G.Adj] in
/-- A maximum path contains all neighbours of its last vertex. -/
lemma last_neighbors_mem {L : List V} (hnd : L.Nodup) (hch : List.IsChain G.Adj L)
    (hmax : ∀ M : List V, M.Nodup → List.IsChain G.Adj M → M.length ≤ L.length)
    {b : V} (hb : L.getLast? = some b) {w : V} (hw : G.Adj b w) : w ∈ L := by
  by_contra hmem
  have hM : (L ++ [w]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    rintro x hx y hy rfl
    simp at hy
    exact hmem (hy ▸ hx)
  have hC : List.IsChain G.Adj (L ++ [w]) := by
    rw [List.isChain_append]
    refine ⟨hch, by simp, ?_⟩
    intro x hx y hy
    rw [hb] at hx
    cases hx
    simp at hy
    cases hy
    exact hw
  have := hmax _ hM hC
  simp at this

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Given a path from `a` to `b` and a position `i` with `a ~ L[i]` and `L[i-1] ~ b`, the
rotation `L.take i ++ (L.drop i).reverse` is a cycle through the same vertices. -/
lemma cycle_of_crossing {L : List V} (hnd : L.Nodup) (hch : List.IsChain G.Adj L)
    {a b : V} (ha : L.head? = some a) (hb : L.getLast? = some b)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i < L.length)
    (hai : G.Adj a (L.getD i a)) (hib : G.Adj (L.getD (i - 1) a) b) :
    ∃ C : List V, C.Nodup ∧ List.IsChain G.Adj C ∧ C.length = L.length ∧ (∀ v, v ∈ C ↔ v ∈ L) ∧
      C.head? = some a ∧ ∃ l, C.getLast? = some l ∧ G.Adj l a := by
  have hsplit : L.take i ++ L.drop i = L := List.take_append_drop i L
  have hperm : (L.take i ++ (L.drop i).reverse).Perm L := by
    have h1 : (L.take i ++ (L.drop i).reverse).Perm (L.take i ++ L.drop i) :=
      List.Perm.append_left _ (List.reverse_perm _)
    rwa [hsplit] at h1
  have hparts := List.isChain_append.mp (by rw [hsplit]; exact hch)
  have htakehead : (L.take i).head? = some a := by
    rw [List.head?_take]
    split_ifs with h
    · omega
    · exact ha
  have htakelast : (L.take i).getLast? = some (L.getD (i - 1) a) := by
    rw [List.getLast?_take]
    split_ifs with h
    · omega
    · rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
  have hdrophead : (L.drop i).head? = some (L.getD i a) := by
    rw [List.head?_drop, List.getElem?_eq_getElem hi2, List.getD_eq_getElem _ _ hi2]
  have hdroplast : (L.drop i).getLast? = some b := by
    rw [List.getLast?_drop]
    split_ifs with h
    · omega
    · exact hb
  refine ⟨L.take i ++ (L.drop i).reverse, hperm.nodup_iff.mpr hnd, ?_, hperm.length_eq,
    fun v => hperm.mem_iff, ?_, L.getD i a, ?_, hai.symm⟩
  · rw [List.isChain_append]
    refine ⟨hparts.1, List.isChain_reverse.mpr (List.IsChain.imp (fun _ _ h => h.symm) hparts.2.1), ?_⟩
    intro x hx y hy
    rw [htakelast] at hx
    rw [List.head?_reverse, hdroplast] at hy
    cases hx; cases hy
    exact hib
  · rw [List.head?_append, htakehead]
    rfl
  · rw [List.getLast?_append, List.getLast?_reverse, hdrophead]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cycle plus an adjacent outside vertex gives a longer path. -/
lemma longer_path_of_cycle {C : List V} (hnd : C.Nodup) (hch : List.IsChain G.Adj C)
    {a l : V} (ha : C.head? = some a) (hl : C.getLast? = some l) (hla : G.Adj l a)
    {u w : V} (hu : u ∉ C) (hw : w ∈ C) (huw : G.Adj u w) :
    ∃ P : List V, P.Nodup ∧ List.IsChain G.Adj P ∧ P.length = C.length + 1 := by
  obtain ⟨s, t, hCst⟩ := List.append_of_mem hw
  have hparts := List.isChain_append.mp (hCst ▸ hch)
  have hperm : ((w :: t) ++ s).Perm C := by
    rw [hCst]; exact List.perm_append_comm
  have hlastwt : (w :: t).getLast? = some l := by
    rw [hCst, List.getLast?_append] at hl
    have : ((w :: t).getLast?).isSome := by
      cases h : (w :: t).getLast? with
      | none => simp at h
      | some _ => simp
    cases h : (w :: t).getLast? with
    | none => simp [h] at this
    | some x => rw [h] at hl; simpa using hl
  refine ⟨u :: ((w :: t) ++ s), ?_, ?_, by rw [← hperm.length_eq]; simp⟩
  · refine List.nodup_cons.mpr ⟨fun hmem => hu (hperm.mem_iff.mp hmem), ?_⟩
    exact hperm.nodup_iff.mpr hnd
  · rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_append] at hy
      simp only [List.head?_cons, Option.some_or, Option.mem_def, Option.some.injEq] at hy
      cases hy
      exact huw
    · rw [List.isChain_append]
      refine ⟨hparts.2.1, hparts.1, ?_⟩
      intro x hx y hy
      rw [hlastwt] at hx
      cases hx
      have hsa : s.head? = some a := by
        have : s ≠ [] := by
          rintro rfl
          simp at hy
        rw [hCst, List.head?_append] at ha
        cases hs : s.head? with
        | none => exact absurd (List.head?_eq_none_iff.mp hs) this
        | some x => rw [hs] at ha; simpa using ha
      rw [hsa] at hy
      cases hy
      exact hla

/-- Packaging a cycle list into `HasHamiltonianCycle`. -/
lemma hasHamiltonianCycle_of_cycle (C : List V) (hnd : C.Nodup)
    (hlen : C.length = Fintype.card V) (hall : ∀ v : V, v ∈ C) (hch : List.IsChain G.Adj C)
    {a l : V} (ha : C.head? = some a) (hl : C.getLast? = some l) (hla : G.Adj l a) :
    HasHamiltonianCycle G := by
  refine ⟨C, hnd, hlen, hall, hch, ?_⟩
  cases C with
  | nil => simp at ha
  | cons x t =>
      have hxa : x = a := by simpa using ha
      subst hxa
      show match (x :: t).getLast? with | none => False | some l => G.Adj l x
      rw [hl]
      exact hla

end Dirac

/-- **Dirac's Theorem for Regular Graphs (Lovász, Problem 22).** -/
theorem Lovasz_22
    {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (n r : ℕ)
    (hcard : Fintype.card V = 2 * n + 1)
    (hreg  : IsRegularR G r)
    (hdeg  : r ≥ n + 1) :
    HasHamiltonianCycle G := by
  classical
  have hdegs : ∀ v : V, (neighFinset G v).card = r := hreg
  have hVpos : 0 < Fintype.card V := by omega
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp hVpos
  obtain ⟨L, hnd, hch, hmax⟩ := Dirac.exists_max_path G
  have hLmax1 : [v0].length ≤ L.length := hmax [v0] (List.nodup_singleton v0) List.IsChain.nil
  have hLpos : 0 < L.length := by simpa using hLmax1
  obtain ⟨a, ha⟩ : ∃ a, L.head? = some a := by
    cases hL : L with
    | nil => rw [hL] at hLpos; simp at hLpos
    | cons x t => exact ⟨x, by simp⟩
  obtain ⟨b, hb⟩ : ∃ b, L.getLast? = some b := by
    cases hL : L.getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff] at hL
        rw [hL] at hLpos; simp at hLpos
    | some x => exact ⟨x, rfl⟩
  have haL : a ∈ L := List.mem_of_mem_head? ha
  set k := L.length - 1
  have hLk_eq : L.length = k + 1 := by omega
  have hL0 : L.getD 0 a = a := by
    rw [List.getD_eq_getElem _ _ hLpos]
    have h : L[0]? = some a := by rw [← List.head?_eq_getElem?]; exact ha
    rw [List.getElem?_eq_getElem hLpos] at h
    simpa using h
  have hLk : L.getD k a = b := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have h : L[L.length - 1]? = some b := by rw [← List.getLast?_eq_getElem?]; exact hb
    rw [List.getElem?_eq_getElem (by omega)] at h
    simp only [Option.some.injEq] at h
    rw [← h]
  have hna : ∀ w, G.Adj a w → w ∈ L := fun w hw => Dirac.head_neighbors_mem G hnd hch hmax ha hw
  have hnb : ∀ w, G.Adj b w → w ∈ L := fun w hw => Dirac.last_neighbors_mem G hnd hch hmax hb hw
  have hinj : ∀ i, i < L.length → ∀ j, j < L.length → L.getD i a = L.getD j a → i = j := by
    intro i hi j hj h
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    exact hnd.getElem_inj_iff.mp h
  set S := (Finset.Icc 1 k).filter (fun i => G.Adj a (L.getD i a)) with hS
  set T := (Finset.Icc 1 k).filter (fun i => G.Adj b (L.getD (i - 1) a)) with hT
  have hScard : S.card = r := by
    have hinjOn : Set.InjOn (fun i => L.getD i a) S := by
      intro x hx y hy hxy
      rw [hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx hy
      exact hinj x (by omega) y (by omega) hxy
    have himg : S.image (fun i => L.getD i a) = neighFinset G a := by
      ext w
      simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_Icc, Dirac.mem_neighFinset]
      constructor
      · rintro ⟨j, ⟨-, hadj⟩, rfl⟩
        exact hadj
      · intro hadj
        obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp (hna w hadj)
        have hgd : L.getD j a = w := by rw [List.getD_eq_getElem _ _ hj]; exact hjw
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with rfl | h
          · exfalso
            rw [hL0] at hgd
            rw [← hgd] at hadj
            exact G.irrefl hadj
          · exact h
        exact ⟨j, ⟨⟨hj1, by omega⟩, by rw [hgd]; exact hadj⟩, hgd⟩
    have h := hdegs a
    rw [← himg, Finset.card_image_of_injOn hinjOn] at h
    exact h
  have hTcard : T.card = r := by
    have hinjOn : Set.InjOn (fun i => L.getD (i - 1) a) T := by
      intro x hx y hy hxy
      rw [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx hy
      have := hinj (x - 1) (by omega) (y - 1) (by omega) hxy
      omega
    have himg : T.image (fun i => L.getD (i - 1) a) = neighFinset G b := by
      ext w
      simp only [Finset.mem_image, hT, Finset.mem_filter, Finset.mem_Icc, Dirac.mem_neighFinset]
      constructor
      · rintro ⟨j, ⟨-, hadj⟩, rfl⟩
        exact hadj
      · intro hadj
        obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp (hnb w hadj)
        have hgd : L.getD j a = w := by rw [List.getD_eq_getElem _ _ hj]; exact hjw
        have hjk : j ≠ k := by
          rintro rfl
          rw [hLk] at hgd
          rw [← hgd] at hadj
          exact G.irrefl hadj
        refine ⟨j + 1, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩ <;>
          simp only [Nat.add_sub_cancel, hgd]
        exact hadj
    have h := hdegs b
    rw [← himg, Finset.card_image_of_injOn hinjOn] at h
    exact h
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr (fun x hx hx' => hcon x hx hx')
    have hsub : S ∪ T ⊆ Finset.Icc 1 k :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcards := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hScard, hTcard, Nat.card_Icc] at hcards
    have : L.length ≤ 2 * n + 1 := by
      rw [← hcard]
      exact hnd.length_le_card
    omega
  simp only [hS, hT, Finset.mem_filter, Finset.mem_Icc] at hiS hiT
  obtain ⟨⟨hi1, hi2⟩, hadj1⟩ := hiS
  obtain ⟨-, hadj2⟩ := hiT
  obtain ⟨C, hCnd, hCch, hClen, -, hCa, l, hCl, hla⟩ :=
    Dirac.cycle_of_crossing G hnd hch ha hb hi1 (by omega) hadj1 hadj2.symm
  have hall : ∀ v : V, v ∈ C := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := hcon
    have hex : ∃ w, w ∈ C ∧ G.Adj u w := by
      by_contra hno
      push Not at hno
      have hsub : insert u (neighFinset G u) ⊆ Finset.univ \ C.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Dirac.mem_neighFinset] at hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_toFinset]
        rcases hx with rfl | hx
        · exact hu
        · exact fun hc => (hno x hc) hx
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [Dirac.mem_neighFinset]),
        Finset.card_univ_sdiff, List.toFinset_card_of_nodup hCnd,
        hdegs u, hcard] at h1
      omega
    obtain ⟨w, hwC, huw⟩ := hex
    obtain ⟨P, hP1, hP2, hP3⟩ := Dirac.longer_path_of_cycle G hCnd hCch hCa hCl hla hu hwC huw
    have hmaxP := hmax P hP1 hP2
    omega
  have hCcard : C.length = Fintype.card V := by
    have huniv : C.toFinset = Finset.univ := by
      ext x
      simp [List.mem_toFinset, hall x]
    rw [← List.toFinset_card_of_nodup hCnd, huniv, Finset.card_univ]
  exact Dirac.hasHamiltonianCycle_of_cycle G C hCnd hCcard hall hCch hCa hCl hla

/-- Answer to the accompanying multiple-choice question: **(a) Dirac's theorem**. -/
def Lovasz_22_answer : String := "(a) Dirac's theorem"
