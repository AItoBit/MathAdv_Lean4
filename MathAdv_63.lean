import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Conjugate (Ferrers) partitions

We show that the number of partitions of `n` into at most `r` parts equals the number of
partitions of `n` into parts each of size at most `r`, by exhibiting the classical bijection
given by transposing the Ferrers diagram.
-/

/-- The multiple choice answer. -/
def Lovasz_12_answer : String := "(d) Ferrer diagram"

/-- A partition of `n`: a nonincreasing list of positive integers summing to `n`. -/
structure IntPartition (n : ℕ) where
  parts   : List ℕ
  pos     : ∀ a ∈ parts, 0 < a
  sum_eq  : parts.sum = n
  noninc  : parts.Pairwise (· ≥ ·)

/-- Partitions of `n` into at most `r` parts. -/
def PartitionsLenLe (n r : ℕ) : Type :=
  { p : IntPartition n // p.parts.length ≤ r }

/-- Partitions of `n` all of whose parts are at most `r`. -/
def PartitionsPartsLe (n r : ℕ) : Type :=
  { p : IntPartition n // ∀ a ∈ p.parts, a ≤ r }

namespace Ferrers

/-- The conjugate of a list of parts: the `j`-th entry (for `j` below the first part) counts the
parts that are `> j`. For a nonincreasing list this is the transpose of the Ferrers diagram. -/
def conj (L : List ℕ) : List ℕ :=
  (List.range L.headI).map (fun j => L.countP (fun a => decide (j < a)))

lemma conj_length (L : List ℕ) : (conj L).length = L.headI := by
  simp [conj]

lemma conj_getElem (L : List ℕ) (j : ℕ) (hj : j < (conj L).length) :
    (conj L)[j] = L.countP (fun a => decide (j < a)) := by
  simp only [conj, List.length_map, List.length_range] at hj
  simp only [conj, List.getElem_map, List.getElem_range]

lemma headI_eq_getElem (L : List ℕ) (h : 0 < L.length) : L.headI = L[0] := by
  cases L with
  | nil => simp at h
  | cons a t => simp

/-- In a nonincreasing list, every element is at most the head. -/
lemma le_head_of_mem {a : ℕ} {t : List ℕ} (h : (a :: t).Pairwise (· ≥ ·)) :
    ∀ b ∈ t, b ≤ a := by
  intro b hb
  exact (List.pairwise_cons.mp h).1 b hb

/-- Key counting lemma: for a nonincreasing list, `k < #{ parts > j }` iff the `k`-th part is
`> j`. -/
lemma lt_countP_iff (L : List ℕ) (h : L.Pairwise (· ≥ ·)) (j k : ℕ) (hk : k < L.length) :
    k < L.countP (fun a => decide (j < a)) ↔ j < L[k] := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    have hle : ∀ b ∈ t, b ≤ a := le_head_of_mem h
    have ht : t.Pairwise (· ≥ ·) := h.tail
    rcases Nat.eq_zero_or_pos k with rfl | _
    · simp only [List.getElem_cons_zero, List.countP_cons]
      by_cases hja : j < a
      · simp [hja]
      · have h0 : t.countP (fun b => decide (j < b)) = 0 := by
          rw [List.countP_eq_zero]
          intro b hb
          have : b ≤ a := hle b hb
          simp only [decide_eq_true_eq]
          omega
        simp [hja, h0]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hk' : m < t.length := by simpa using hk
      simp only [List.getElem_cons_succ, List.countP_cons]
      by_cases hja : j < a
      · simp only [hja, decide_true, ite_true]
        rw [← ih ht m hk']
        omega
      · have h0 : t.countP (fun b => decide (j < b)) = 0 := by
          rw [List.countP_eq_zero]
          intro b hb
          have : b ≤ a := hle b hb
          simp only [decide_eq_true_eq]
          omega
        have hta : t[m] ≤ a := hle _ (List.getElem_mem hk')
        have hfalse : ¬ (j < t[m]) := by omega
        simp [hja, h0, hfalse]

/-- Every entry of a nonincreasing list is at most its head. -/
lemma getElem_le_headI (L : List ℕ) (h : L.Pairwise (· ≥ ·)) (k : ℕ) (hk : k < L.length) :
    L[k] ≤ L.headI := by
  cases L with
  | nil => simp at hk
  | cons a t =>
    simp only [List.headI]
    rcases Nat.eq_zero_or_pos k with rfl | _
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm : m < t.length := by simpa using hk
      have : (a :: t)[m + 1] = t[m] := by simp
      rw [this]
      exact le_head_of_mem h _ (List.getElem_mem hm)

lemma conj_pos (L : List ℕ) (h : L.Pairwise (· ≥ ·)) : ∀ a ∈ conj L, 0 < a := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  rw [conj_getElem L j hj]
  rw [conj_length] at hj
  have hL : L ≠ [] := by
    rintro rfl
    simp [List.headI] at hj
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  rw [lt_countP_iff L h j 0 hlen]
  rw [headI_eq_getElem L hlen] at hj
  exact hj

lemma conj_chain (L : List ℕ) : (conj L).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hij hj
  have hi : i < (conj L).length := lt_trans hij hj
  rw [conj_getElem L i hi, conj_getElem L j hj]
  exact List.countP_mono_left (by intro x _ hx; simp only [decide_eq_true_eq] at hx ⊢; omega)

lemma sum_conj (L : List ℕ) (h : L.Pairwise (· ≥ ·)) : (conj L).sum = L.sum := by
  have key : ∀ (M : ℕ) (K : List ℕ), (∀ a ∈ K, a ≤ M) →
      (∑ j ∈ Finset.range M, K.countP (fun a => decide (j < a))) = K.sum := by
    intro M K
    induction K with
    | nil => intro _; simp
    | cons a t ih =>
      intro hall
      have hat : ∀ b ∈ t, b ≤ M := fun b hb => hall b (List.mem_cons_of_mem _ hb)
      have hcongr : ∀ j ∈ Finset.range M,
          (a :: t).countP (fun x => decide (j < x))
            = t.countP (fun x => decide (j < x)) + (if j < a then 1 else 0) := by
        intro j _
        simp only [List.countP_cons, decide_eq_true_eq]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ih hat]
      have hind : ∑ j ∈ Finset.range M, (if j < a then 1 else 0) = a := by
        have haM : a ≤ M := hall a (List.mem_cons_self ..)
        have hfilter : (Finset.filter (fun x => x < a) (Finset.range M)) = Finset.range a := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun hx => hx.2, fun hx => ⟨lt_of_lt_of_le hx haM, hx⟩⟩
        have hsum_if := Finset.sum_boole (fun x => x < a) (Finset.range M)
        rw [hsum_if, hfilter, Finset.card_range]
      rw [hind, List.sum_cons]
      omega
  have hall : ∀ a ∈ L, a ≤ L.headI := by
    cases L with
    | nil => simp
    | cons a t =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp
      · simpa using le_head_of_mem h b hb
  have hlist : (conj L).sum
      = ∑ j ∈ Finset.range L.headI, L.countP (fun a => decide (j < a)) := by
    simp [conj, Finset.sum, Finset.range, Multiset.sum, Multiset.range, List.sum_eq_foldr]
  rw [hlist]
  exact key L.headI L hall

lemma conj_headI (L : List ℕ) (hpos : ∀ a ∈ L, 0 < a) : (conj L).headI = L.length := by
  rcases eq_or_ne L [] with rfl | hL
  · simp [conj]
  · have hLlen : 0 < L.length := List.length_pos_iff.mpr hL
    have h0 : 0 < (conj L).length := by
      rw [conj_length, headI_eq_getElem L hLlen]
      exact hpos _ (List.getElem_mem hLlen)
    rw [headI_eq_getElem _ h0, conj_getElem L 0 h0, List.countP_eq_length]
    intro a ha
    simpa using hpos a ha

lemma conj_conj (L : List ℕ) (h : L.Pairwise (· ≥ ·)) (hpos : ∀ a ∈ L, 0 < a) :
    conj (conj L) = L := by
  have hlen : (conj L).length = L.headI := conj_length L
  have hchain : (conj L).Pairwise (· ≥ ·) := conj_chain L
  have hhead : (conj L).headI = L.length := conj_headI L hpos
  apply List.ext_getElem
  · rw [conj_length, hhead]
  · intro k hk_conj hk_L
    rw [conj_getElem _ k hk_conj]
    set X := (conj L).countP (fun c => decide (k < c)) with hX
    have hXle : X ≤ L.headI := by
      rw [hX]
      calc (conj L).countP (fun c => decide (k < c)) ≤ (conj L).length :=
        List.countP_le_length
      _ = L.headI := hlen
    have hLk : L[k] ≤ L.headI := getElem_le_headI L h k hk_L
    have main : ∀ m, m < L.headI → (m < X ↔ m < L[k]) := by
      intro m hm
      have hm' : m < (conj L).length := by rw [hlen]; exact hm
      rw [hX, lt_countP_iff (conj L) hchain k m hm', conj_getElem L m hm']
      exact lt_countP_iff L h m k hk_L
    by_contra hne
    rcases Nat.lt_or_ge X L[k] with hc | hc
    · have h1 := (main X (by omega)).mp (Nat.lt_succ_self X)
      omega
    · have hne' : X ≠ L[k] := hne
      have hlt : L[k] < X := lt_of_le_of_ne hc hne'.symm
      have h1 := (main L[k] (by omega)).mpr (Nat.lt_succ_self (L[k]))
      omega

end Ferrers

open Ferrers in
/-- Conjugation as a map on partitions of `n`. -/
def IntPartition.conjugate {n : ℕ} (p : IntPartition n) : IntPartition n where
  parts := conj p.parts
  pos := conj_pos p.parts p.noninc
  sum_eq := by rw [sum_conj p.parts p.noninc]; exact p.sum_eq
  noninc := conj_chain p.parts

open Ferrers in
theorem IntPartition.conjugate_conjugate {n : ℕ} (p : IntPartition n) :
    p.conjugate.conjugate = p := by
  cases p with
  | mk parts pos sum_eq noninc =>
    simp only [IntPartition.conjugate, IntPartition.mk.injEq]
    exact conj_conj parts noninc pos

/-- **Conjugation bijection**: the partitions of `n` into at most `r` parts are in bijection with
the partitions of `n` into parts of size at most `r`. -/
theorem Lovasz_12 (n r : ℕ) :
    Nonempty (PartitionsLenLe n r ≃ PartitionsPartsLe n r) := by
  classical
  refine ⟨⟨fun p => ⟨p.1.conjugate, ?_⟩, fun q => ⟨q.1.conjugate, ?_⟩, ?_, ?_⟩⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hj' : j < (Ferrers.conj p.1.parts).length := by
      rw [Ferrers.conj_length]
      exact hj
    show (Ferrers.conj p.1.parts)[j] ≤ r
    rw [Ferrers.conj_getElem _ j hj']
    exact le_trans List.countP_le_length p.2
  · show (Ferrers.conj q.1.parts).length ≤ r
    rw [Ferrers.conj_length]
    cases hL : q.1.parts with
    | nil => simp
    | cons a t =>
      have : a ∈ q.1.parts := by rw [hL]; exact List.mem_cons_self ..
      simpa [hL] using q.2 a this
  · intro p
    exact Subtype.ext (IntPartition.conjugate_conjugate p.1)
  · intro q
    exact Subtype.ext (IntPartition.conjugate_conjugate q.1)
