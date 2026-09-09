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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Problem21

open Finset

/-! ### A convolution identity for central binomial coefficients -/

private lemma sum_sym (m : ℕ) :
    ∑ k ∈ range (m + 1), k * (Nat.centralBinom k * Nat.centralBinom (m - k))
      = ∑ k ∈ range (m + 1), (m - k) * (Nat.centralBinom k * Nat.centralBinom (m - k)) := by
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [mem_range] at hj
  have h1 : m + 1 - 1 - j = m - j := by omega
  have h2 : m - (m - j) = j := by omega
  rw [h1, h2]; ring

private lemma two_mul_wsum (m : ℕ) :
    2 * ∑ k ∈ range (m + 1), k * (Nat.centralBinom k * Nat.centralBinom (m - k))
      = m * ∑ k ∈ range (m + 1), Nat.centralBinom k * Nat.centralBinom (m - k) := by
  have h := sum_sym m
  rw [two_mul]
  nth_rewrite 2 [h]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [mem_range] at hj
  have hj' : j + (m - j) = m := by omega
  rw [← add_mul, hj']

/-- `∑_{k=0}^{n} C(2k,k) C(2n-2k, n-k) = 4^n`. -/
theorem centralBinom_convolution (n : ℕ) :
    ∑ k ∈ range (n + 1), Nat.centralBinom k * Nat.centralBinom (n - k) = 4 ^ n := by
  induction n with
  | zero => simp [Nat.centralBinom]
  | succ n ih =>
    have key : (n + 1) * ∑ k ∈ range (n + 2), Nat.centralBinom k * Nat.centralBinom (n + 1 - k)
        = (n + 1) * (4 * 4 ^ n) := by
      rw [← two_mul_wsum (n + 1)]
      rw [Finset.sum_range_succ'
        (fun k => k * (Nat.centralBinom k * Nat.centralBinom (n + 1 - k))) (n + 1)]
      have hterm : ∀ j ∈ range (n + 1),
          (j + 1) * (Nat.centralBinom (j + 1) * Nat.centralBinom (n + 1 - (j + 1)))
            = 4 * (j * (Nat.centralBinom j * Nat.centralBinom (n - j)))
              + 2 * (Nat.centralBinom j * Nat.centralBinom (n - j)) := by
        intro j _
        have h1 : n + 1 - (j + 1) = n - j := by omega
        rw [h1, ← mul_assoc, Nat.succ_mul_centralBinom_succ j]
        ring
      rw [Finset.sum_congr rfl hterm]
      simp only [zero_mul, add_zero]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ih,
        show (4 : ℕ) * ∑ k ∈ range (n + 1), k * (Nat.centralBinom k * Nat.centralBinom (n - k))
            = 2 * (2 * ∑ k ∈ range (n + 1),
                k * (Nat.centralBinom k * Nat.centralBinom (n - k))) by ring,
        two_mul_wsum n, ih]
      ring
    have h := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) key
    rw [h]; ring

/-! ### Counting lemmas -/

/-- Boolean functions with a prescribed property of their "true set" are counted by
the corresponding sets. -/
theorem card_fun_eq_card_set {α : Type*} [Fintype α] [DecidableEq α] (p : Finset α → Prop)
    [DecidablePred p] :
    (univ.filter (fun f : α → Bool => p (univ.filter (fun j => f j = true)))).card
      = (univ.filter (fun S : Finset α => p S)).card := by
  have hset : ∀ S : Finset α, (univ.filter (fun j => (decide (j ∈ S)) = true)) = S := by
    intro S; ext a; simp
  apply Finset.card_bij' (fun f _ => univ.filter (fun j => f j = true))
    (fun S _ => fun a => decide (a ∈ S))
  case hi => intro f hf; simpa using (mem_filter.mp hf).2
  case hj =>
    intro S hS
    have hp := (mem_filter.mp hS).2
    simp only [mem_filter, mem_univ, true_and, hset]
    exact hp
  case left_inv => intro f _; funext a; simp
  case right_inv => intro S _; exact hset S

/-- The number of `n`-element subsets meeting a fixed set `P` in exactly `k` elements. -/
theorem card_set_split {α : Type*} [Fintype α] [DecidableEq α] (P : Finset α) (n k : ℕ)
    (hk : k ≤ n) :
    (univ.filter (fun S : Finset α => S.card = n ∧ (S ∩ P).card = k)).card
      = P.card.choose k * Pᶜ.card.choose (n - k) := by
  rw [← Finset.card_powersetCard k P, ← Finset.card_powersetCard (n - k) Pᶜ,
    ← Finset.card_product]
  apply Finset.card_bij' (fun S _ => (S ∩ P, S \ P)) (fun st _ => st.1 ∪ st.2)
  case hi =>
    intro S hS
    obtain ⟨h1, h2⟩ := (mem_filter.mp hS).2
    have h3 := Finset.card_sdiff_add_card_inter S P
    simp only [mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_right, h2⟩, ?_, by omega⟩
    intro a ha; simp only [mem_sdiff] at ha; simpa using ha.2
  case hj =>
    intro st hst
    simp only [mem_product, mem_powersetCard] at hst
    obtain ⟨⟨hs1, hs2⟩, ht1, ht2⟩ := hst
    have h2P : st.2 ∩ P = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      simp only [Finset.mem_inter] at ha
      have hc := ht1 ha.1
      simp only [Finset.mem_compl] at hc
      exact hc ha.2
    have hdisj : Disjoint st.1 st.2 := by
      refine Finset.disjoint_left.mpr ?_
      intro a ha1 ha2
      have hc := ht1 ha2
      simp only [mem_compl] at hc
      exact hc (hs1 ha1)
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨by rw [Finset.card_union_of_disjoint hdisj, hs2, ht2]; omega, ?_⟩
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs1, h2P,
      Finset.union_empty, hs2]
  case left_inv =>
    intro S _; ext a; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  case right_inv =>
    intro st hst
    simp only [mem_product, mem_powersetCard] at hst
    obtain ⟨⟨hs1, hs2⟩, ht1, ht2⟩ := hst
    have h2P : st.2 ∩ P = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      simp only [Finset.mem_inter] at ha
      have hc := ht1 ha.1
      simp only [Finset.mem_compl] at hc
      exact hc ha.2
    have h1 : (st.1 ∪ st.2) ∩ P = st.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs1, h2P,
        Finset.union_empty]
    have h2 : (st.1 ∪ st.2) \ P = st.2 := by
      ext a
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h | h, hP⟩
        · exact absurd (hs1 h) hP
        · exact h
      · intro h
        refine ⟨Or.inr h, ?_⟩
        have hc := ht1 h; simp only [mem_compl] at hc; exact hc
    rw [h1, h2]

/-- Cardinality of an initial segment of `Fin m`. -/
theorem card_pref (m i : ℕ) (hi : i ≤ m) :
    (univ.filter (fun j : Fin m => (j : ℕ) < i)).card = i := by
  have himg : (univ.filter (fun j : Fin m => (j : ℕ) < i)).image (Fin.val) = range i := by
    ext a
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
  have h := Finset.card_image_of_injective
    (univ.filter (fun j : Fin m => (j : ℕ) < i)) Fin.val_injective
  rw [himg, card_range] at h
  exact h.symm


/-! ### The score of a single deal -/

/-- The number of red (`true`) cards among the first `i` cards of the deal `f`. -/
def cnt (n : ℕ) (f : Fin (2 * n) → Bool) (i : ℕ) : ℕ :=
  ((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)).filter (fun j => f j = true)).card

/-- The absolute difference between the numbers of red and black cards among the first
`i` cards of the deal `f`. -/
noncomputable def D (n : ℕ) (f : Fin (2 * n) → Bool) (i : ℕ) : ℝ :=
  |2 * (cnt n f i : ℝ) - (i : ℝ)|

variable {n : ℕ}

lemma cnt_zero (f : Fin (2 * n) → Bool) : cnt n f 0 = 0 := by simp [cnt]

lemma cnt_succ (f : Fin (2 * n) → Bool) (i : ℕ) (hi : i < 2 * n) :
    cnt n f (i + 1) = cnt n f i + (if f ⟨i, hi⟩ = true then 1 else 0) := by
  have hins : (univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i + 1))
      = insert (⟨i, hi⟩ : Fin (2 * n)) (univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  unfold cnt
  rw [hins, Finset.filter_insert]
  by_cases h : f ⟨i, hi⟩ = true
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

lemma cnt_le (f : Fin (2 * n) → Bool) (i : ℕ) :
    cnt n f i ≤ (univ.filter (fun j : Fin (2 * n) => f j = true)).card := by
  apply Finset.card_le_card
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at *
  exact ha.2

lemma cnt_end (f : Fin (2 * n) → Bool) :
    cnt n f (2 * n) = (univ.filter (fun j : Fin (2 * n) => f j = true)).card := by
  unfold cnt
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨a.isLt, h⟩⟩

lemma blk_eq (f : Fin (2 * n) → Bool) (i : ℕ) (hi : i ≤ 2 * n) :
    (((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)).filter (fun j => f j = false)).card)
      + cnt n f i = i := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i))) (p := fun j => f j = false)
  have h2 : ((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)).filter
      (fun j => ¬ (f j = false))).card = cnt n f i := by
    unfold cnt; congr 1; apply Finset.filter_congr; intro x _; simp
  rw [h2, card_pref (2 * n) i hi] at h
  exact h

lemma blk_le (f : Fin (2 * n) → Bool) (i : ℕ)
    (hf : (univ.filter (fun j : Fin (2 * n) => f j = true)).card = n) :
    (((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)).filter
      (fun j => f j = false)).card) ≤ n := by
  have h1 : (((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i)).filter
      (fun j => f j = false)).card)
      ≤ (univ.filter (fun j : Fin (2 * n) => f j = false)).card := by
    apply Finset.card_le_card
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at *
    exact ha.2
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * n))))
      (p := fun j => f j = true)
  have heq : (univ.filter (fun j : Fin (2 * n) => ¬ (f j = true)))
      = (univ.filter (fun j : Fin (2 * n) => f j = false)) := by
    apply Finset.filter_congr; intro x _; simp
  rw [heq, Finset.card_univ, Fintype.card_fin, hf] at h2
  omega

/-- The expected score gained on the `i`-th card, expressed through the telescoping
quantity `D` and the indicator of a tie. -/
theorem summand_eq (f : Fin (2 * n) → Bool)
    (hf : (univ.filter (fun j : Fin (2 * n) => f j = true)).card = n) (i : Fin (2 * n)) :
    (let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
     let rem_red := n - (past.filter (fun j => f j = true)).card
     let rem_black := n - (past.filter (fun j => f j = false)).card
     if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
     else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
     else 0.5)
      = (1 / 2) * (D n f (i : ℕ) - D n f ((i : ℕ) + 1)) + 1 / 2
        + (if 2 * cnt n f (i : ℕ) = (i : ℕ) then (1 / 2 : ℝ) else 0) := by
  have hpast : (Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ)
      = (univ.filter (fun j : Fin (2 * n) => (j : ℕ) < (i : ℕ))) := by
    apply Finset.filter_congr; intro x _; simp only [Fin.lt_def]
  simp only [hpast]
  set c := cnt n f (i : ℕ) with hc
  set b := (((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < (i : ℕ))).filter
    (fun j => f j = false)).card) with hb
  have hcdef : ((univ.filter (fun j : Fin (2 * n) => (j : ℕ) < (i : ℕ))).filter
      (fun j => f j = true)).card = c := rfl
  rw [hcdef]
  have hbc : b + c = (i : ℕ) := blk_eq f (i : ℕ) (le_of_lt i.isLt)
  have hcn : c ≤ n := by have h := cnt_le f (i : ℕ); rw [hf] at h; exact h
  have hbn : b ≤ n := blk_le f (i : ℕ) hf
  have hsucc : cnt n f ((i : ℕ) + 1) = c + (if f i = true then 1 else 0) := by
    have h := cnt_succ f (i : ℕ) i.isLt
    simpa using h
  have hDi : D n f (i : ℕ) = |2 * (c : ℝ) - ((i : ℕ) : ℝ)| := rfl
  by_cases hfi : f i = true
  · have hfi2 : ¬ (f i = false) := by simp [hfi]
    have hDs : D n f ((i : ℕ) + 1) = |2 * ((c : ℝ) + 1) - (((i : ℕ) : ℝ) + 1)| := by
      unfold D; rw [hsucc, if_pos hfi]; push_cast; ring_nf
    rw [hDi, hDs]
    rcases lt_trichotomy (2 * c) (i : ℕ) with h | h | h
    · rw [if_pos (by omega), if_pos hfi, if_neg (by omega : ¬ (2 * c = (i : ℕ)))]
      have e1 : |2 * (c : ℝ) - ((i : ℕ) : ℝ)| = ((i : ℕ) : ℝ) - 2 * c := by
        have hle : (2 * c : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h.le
        rw [abs_of_nonpos (by linarith)]; ring
      have e2 : |2 * ((c : ℝ) + 1) - (((i : ℕ) : ℝ) + 1)| = ((i : ℕ) : ℝ) - 2 * c - 1 := by
        have hle : (2 * c : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]; ring
      rw [e1, e2]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have hr : ((i : ℕ) : ℝ) = 2 * c := by exact_mod_cast h.symm
      rw [hr, show |2 * (c : ℝ) - 2 * c| = 0 by simp,
        show |2 * ((c : ℝ) + 1) - (2 * (c : ℝ) + 1)| = 1 by
          rw [show 2 * ((c : ℝ) + 1) - (2 * (c : ℝ) + 1) = 1 by ring]; simp]
      norm_num
    · rw [if_neg (by omega), if_pos (by omega), if_neg hfi2,
        if_neg (by omega : ¬ (2 * c = (i : ℕ)))]
      have hle : ((i : ℕ) : ℝ) ≤ 2 * c := by exact_mod_cast h.le
      have e1 : |2 * (c : ℝ) - ((i : ℕ) : ℝ)| = 2 * (c : ℝ) - ((i : ℕ) : ℝ) :=
        abs_of_nonneg (by linarith)
      have e2 : |2 * ((c : ℝ) + 1) - (((i : ℕ) : ℝ) + 1)| = 2 * (c : ℝ) + 1 - ((i : ℕ) : ℝ) := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [e1, e2]; ring
  · have hfi' : f i = false := by simpa using hfi
    have hDs : D n f ((i : ℕ) + 1) = |2 * (c : ℝ) - (((i : ℕ) : ℝ) + 1)| := by
      unfold D; rw [hsucc, if_neg hfi]; push_cast; ring_nf
    rw [hDi, hDs]
    rcases lt_trichotomy (2 * c) (i : ℕ) with h | h | h
    · rw [if_pos (by omega), if_neg hfi, if_neg (by omega : ¬ (2 * c = (i : ℕ)))]
      have hle : (2 * c : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h.le
      have e1 : |2 * (c : ℝ) - ((i : ℕ) : ℝ)| = ((i : ℕ) : ℝ) - 2 * c := by
        rw [abs_of_nonpos (by linarith)]; ring
      have e2 : |2 * (c : ℝ) - (((i : ℕ) : ℝ) + 1)| = ((i : ℕ) : ℝ) + 1 - 2 * c := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [e1, e2]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have hr : ((i : ℕ) : ℝ) = 2 * c := by exact_mod_cast h.symm
      rw [hr, show |2 * (c : ℝ) - 2 * c| = 0 by simp,
        show |2 * (c : ℝ) - (2 * (c : ℝ) + 1)| = 1 by
          rw [show 2 * (c : ℝ) - (2 * (c : ℝ) + 1) = -1 by ring]; simp]
      norm_num
    · rw [if_neg (by omega), if_pos (by omega), if_pos hfi',
        if_neg (by omega : ¬ (2 * c = (i : ℕ)))]
      have hle : ((i : ℕ) : ℝ) + 1 ≤ 2 * c := by exact_mod_cast h
      have e1 : |2 * (c : ℝ) - ((i : ℕ) : ℝ)| = 2 * (c : ℝ) - ((i : ℕ) : ℝ) :=
        abs_of_nonneg (by linarith)
      have e2 : |2 * (c : ℝ) - (((i : ℕ) : ℝ) + 1)| = 2 * (c : ℝ) - ((i : ℕ) : ℝ) - 1 := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [e1, e2]; ring

/-- The parent's score on a given deal is `n` plus half the number of "ties",
i.e. of the moments at which equally many red and black cards have been turned up. -/
theorem score_eq (f : Fin (2 * n) → Bool)
    (hf : (univ.filter (fun j : Fin (2 * n) => f j = true)).card = n) :
    (∑ i : Fin (2 * n),
      let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
      let rem_red := n - (past.filter (fun j => f j = true)).card
      let rem_black := n - (past.filter (fun j => f j = false)).card
      if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
      else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
      else 0.5)
      = n + (1 / 2) * (((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => summand_eq f hf i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => (1 / 2) * (D n f i - D n f (i + 1)) + 1 / 2
        + (if 2 * cnt n f i = i then (1 / 2 : ℝ) else 0)) (2 * n)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have t1 : ∑ i ∈ range (2 * n), (1 / 2 : ℝ) * (D n f i - D n f (i + 1)) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i => D n f i) (2 * n)]
    have h0 : D n f 0 = 0 := by simp [D, cnt_zero]
    have h1 : D n f (2 * n) = 0 := by simp [D, cnt_end f, hf]
    rw [h0, h1]; ring
  have t2 : ∑ _i ∈ range (2 * n), (1 / 2 : ℝ) = n := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    push_cast; ring
  have t3 : ∑ i ∈ range (2 * n), (if 2 * cnt n f i = i then (1 / 2 : ℝ) else 0)
      = (1 / 2) * (((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
  rw [t1, t2, t3]; ring

/-! ### Counting the ties -/

lemma cnt_inter (f : Fin (2 * n) → Bool) (i : ℕ) :
    cnt n f i = ((univ.filter (fun j : Fin (2 * n) => f j = true))
      ∩ (univ.filter (fun j : Fin (2 * n) => (j : ℕ) < i))).card := by
  unfold cnt
  congr 1
  ext a
  simp only [mem_filter, mem_inter, mem_univ, true_and]
  tauto

/-- The number of deals having a tie after `2 * k` cards. -/
theorem count_tie (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f (2 * k) = 2 * k)).card
      = Nat.centralBinom k * Nat.centralBinom (n - k) := by
  set P : Finset (Fin (2 * n)) := univ.filter (fun j : Fin (2 * n) => (j : ℕ) < 2 * k) with hP
  rw [Finset.filter_filter]
  have hpred : ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n ∧ 2 * cnt n f (2 * k) = 2 * k)))
      = (univ.filter (fun f : Fin (2 * n) → Bool =>
        ((univ.filter (fun j => f j = true)).card = n ∧
          (((univ.filter (fun j => f j = true))) ∩ P).card = k))) := by
    apply Finset.filter_congr
    intro f _
    rw [cnt_inter f (2 * k), ← hP]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  rw [hpred, card_fun_eq_card_set (fun S : Finset (Fin (2 * n)) => S.card = n ∧ (S ∩ P).card = k),
    card_set_split P n k hk]
  have hPcard : P.card = 2 * k := by rw [hP]; exact card_pref (2 * n) (2 * k) (by omega)
  have hPc : Pᶜ.card = 2 * (n - k) := by
    rw [Finset.card_compl, hPcard, Fintype.card_fin]; omega
  rw [hPcard, hPc]
  rfl

/-- There is never a tie after an odd number of cards. -/
theorem count_odd (n k : ℕ) :
    ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f (2 * k + 1) = 2 * k + 1)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _
  omega

/-- The number of deals is the central binomial coefficient. -/
theorem card_Omega (n : ℕ) :
    (univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).card = (2 * n).choose n := by
  rw [card_fun_eq_card_set (fun S : Finset (Fin (2 * n)) => S.card = n)]
  have h : (univ.filter (fun S : Finset (Fin (2 * n)) => S.card = n)) = powersetCard n univ := by
    ext S; simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), F i = ∑ k ∈ range m, (F (2 * k) + F (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

/-- The total number of ties over all deals. -/
theorem total_ties (n : ℕ) :
    (∑ f ∈ (univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)),
      ((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card)
      + Nat.centralBinom n = 4 ^ n := by
  have hswap : (∑ f ∈ (univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)),
      ((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card)
      = ∑ i ∈ range (2 * n), ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f i = i)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap, sum_range_two_mul (fun i => ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f i = i)).card) n]
  have hterm : ∀ k ∈ range n,
      ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f (2 * k) = 2 * k)).card
      + ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun j => f j = true)).card = n)).filter
        (fun f => 2 * cnt n f (2 * k + 1) = 2 * k + 1)).card
      = Nat.centralBinom k * Nat.centralBinom (n - k) := by
    intro k hk
    simp only [mem_range] at hk
    rw [count_tie n k (le_of_lt hk), count_odd n k, add_zero]
  rw [Finset.sum_congr rfl hterm]
  have hconv := centralBinom_convolution n
  rw [Finset.sum_range_succ] at hconv
  simpa [Nat.centralBinom] using hconv

/-- The expected number of correct guesses made by the parent. -/
theorem expected_score_eq (n : ℕ) :
    (∑ f ∈ (univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun i => f i = true)).card = n)), ∑ i : Fin (2 * n),
      let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
      let rem_red := n - (past.filter (fun j => f j = true)).card
      let rem_black := n - (past.filter (fun j => f j = false)).card
      if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
      else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
      else 0.5) / ((univ.filter (fun f : Fin (2 * n) → Bool =>
        (univ.filter (fun i => f i = true)).card = n)).card : ℝ)
      = n + 0.5 * ((4 ^ n : ℝ) / ((2 * n).choose n : ℝ) - 1) := by
  set Om := (univ.filter (fun f : Fin (2 * n) → Bool =>
    (univ.filter (fun i => f i = true)).card = n)) with hOm
  have hCpos : 0 < (2 * n).choose n := Nat.choose_pos (by omega)
  have hC : (Om.card : ℝ) = ((2 * n).choose n : ℝ) := by rw [hOm, card_Omega n]
  have hscores : ∑ f ∈ Om, (∑ i : Fin (2 * n),
      let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
      let rem_red := n - (past.filter (fun j => f j = true)).card
      let rem_black := n - (past.filter (fun j => f j = false)).card
      if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
      else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
      else 0.5)
      = ∑ f ∈ Om, ((n : ℝ)
        + (1 / 2) * (((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro f hf
    rw [hOm, mem_filter] at hf
    exact score_eq f hf.2
  rw [hscores, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  have hties : (∑ f ∈ Om, (((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card : ℝ))
      = ((4 : ℝ) ^ n - ((2 * n).choose n : ℝ)) := by
    have h := total_ties n
    rw [← hOm] at h
    have h2 : ((∑ f ∈ Om, ((range (2 * n)).filter (fun i => 2 * cnt n f i = i)).card : ℕ) : ℝ)
        + ((2 * n).choose n : ℝ) = ((4 : ℝ) ^ n) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h
      push_cast at this
      simpa [Nat.centralBinom] using this
    push_cast at h2 ⊢
    linarith
  rw [hties, hC]
  have hCR : ((2 * n).choose n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem problem_21
  (n : ℕ) :
  let Ω : Finset (Fin (2 * n) → Bool) :=
    Finset.univ.filter (fun f => (Finset.univ.filter (fun i => f i = true)).card = n)
  let expected_score : ℝ := (∑ f ∈ Ω, ∑ i : Fin (2 * n),
    let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
    let rem_red := n - (past.filter (fun j => f j = true)).card
    let rem_black := n - (past.filter (fun j => f j = false)).card
    if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
    else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
    else 0.5) / Ω.card
  expected_score = n + 0.5 * ((4^n : ℝ) / (Nat.choose (2 * n) n : ℝ) - 1) := by
  intro Ω expected_score
  exact expected_score_eq n

end Problem21
