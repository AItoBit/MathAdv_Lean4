import Mathlib

/-!
# Expected number of adjacent matching pairs

A general framework: an arrangement of 12 objects in a row is a function `v : Fin 12 → α`
(the object in each of the 12 positions).  Each object has a "key" `key : α → β`
(its rank, or the couple it belongs to).  If the set `V` of admissible arrangements is
invariant under permuting the positions, and if in every admissible arrangement each object
shares its key with exactly one other object (i.e. exactly two positions carry any given key
that occurs), then the average over `V` of the number of adjacent positions carrying equal
keys is exactly `1`.
-/

open Finset

namespace AdjacentPairs

/-- The symmetric group of a type with decidable equality is 2-transitive. -/
lemma exists_perm_apply_apply {γ : Type*} [DecidableEq γ] {a b a' b' : γ}
    (hab : a ≠ b) (hab' : a' ≠ b') : ∃ ρ : Equiv.Perm γ, ρ a = a' ∧ ρ b = b' := by
  set y := Equiv.swap a a' b with hy
  have hy1 : y ≠ a' := by
    rw [hy]
    intro h
    have h2 : Equiv.swap a a' b = Equiv.swap a a' a := by rw [h, Equiv.swap_apply_left]
    exact hab ((Equiv.swap a a').injective h2).symm
  refine ⟨Equiv.swap y b' * Equiv.swap a a', ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hy1) hab'
  · simp only [Equiv.Perm.mul_apply, ← hy, Equiv.swap_apply_left]

variable {α β : Type*} [DecidableEq β] (key : α → β) (V : Finset (Fin 12 → α))

/-- The number of admissible arrangements in which positions `a` and `b` carry the same key. -/
def matchCount (a b : Fin 12) : ℕ := (V.filter (fun v => key (v a) = key (v b))).card

variable {key V}

/-- `matchCount` is invariant under permuting positions. -/
lemma matchCount_perm (hinv : ∀ (ρ : Equiv.Perm (Fin 12)) (v : Fin 12 → α), v ∈ V → v ∘ ρ ∈ V)
    (ρ : Equiv.Perm (Fin 12)) (a b : Fin 12) :
    matchCount key V (ρ a) (ρ b) = matchCount key V a b := by
  refine Finset.card_bij' (fun v _ => v ∘ ρ) (fun v _ => v ∘ ρ.symm) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [mem_filter] at hv ⊢
    exact ⟨hinv ρ v hv.1, hv.2⟩
  · intro v hv
    simp only [mem_filter, Function.comp_apply, Equiv.symm_apply_apply] at hv ⊢
    exact ⟨hinv ρ.symm v hv.1, by simpa using hv.2⟩
  · intro v _; funext j; simp
  · intro v _; funext j; simp

/-- All pairs of distinct positions are matched equally often. -/
lemma matchCount_eq (hinv : ∀ (ρ : Equiv.Perm (Fin 12)) (v : Fin 12 → α), v ∈ V → v ∘ ρ ∈ V)
    {a b a' b' : Fin 12} (hab : a ≠ b) (hab' : a' ≠ b') :
    matchCount key V a b = matchCount key V a' b' := by
  obtain ⟨ρ, hρa, hρb⟩ := exists_perm_apply_apply hab hab'
  rw [← matchCount_perm hinv ρ a b, hρa, hρb]

/-- In an admissible arrangement, each position is matched by exactly one other position. -/
lemma inner_count (hcount : ∀ v ∈ V, ∀ a : Fin 12,
      (univ.filter (fun b => key (v b) = key (v a))).card = 2) (v : Fin 12 → α) (hv : v ∈ V)
    (a : Fin 12) :
    ∑ b : Fin 12, (if a ≠ b ∧ key (v a) = key (v b) then 1 else 0) = 1 := by
  have hset : (univ.filter (fun b => a ≠ b ∧ key (v a) = key (v b)))
      = (univ.filter (fun b => key (v b) = key (v a))).erase a := by
    ext b
    simp only [mem_filter, mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2.symm⟩
  rw [← Finset.card_filter, hset, Finset.card_erase_of_mem (by simp), hcount v hv a]

/-- Double counting: summing `matchCount` over all ordered pairs of distinct positions
counts, for each admissible arrangement, the `12` ordered matched pairs. -/
lemma sum_matchCount (hcount : ∀ v ∈ V, ∀ a : Fin 12,
      (univ.filter (fun b => key (v b) = key (v a))).card = 2) :
    ∑ a : Fin 12, ∑ b : Fin 12, (if a ≠ b then matchCount key V a b else 0) = 12 * V.card := by
  have h1 : ∀ a b : Fin 12, (if a ≠ b then matchCount key V a b else 0)
      = ∑ v ∈ V, (if a ≠ b ∧ key (v a) = key (v b) then 1 else 0) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · rw [if_pos hab, matchCount, Finset.card_filter]
      exact Finset.sum_congr rfl (fun v _ => by simp [hab])
  calc ∑ a : Fin 12, ∑ b : Fin 12, (if a ≠ b then matchCount key V a b else 0)
      = ∑ a : Fin 12, ∑ b : Fin 12, ∑ v ∈ V,
          (if a ≠ b ∧ key (v a) = key (v b) then 1 else 0) := by
        simp only [h1]
    _ = ∑ a : Fin 12, ∑ v ∈ V, ∑ b : Fin 12,
          (if a ≠ b ∧ key (v a) = key (v b) then 1 else 0) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ v ∈ V, ∑ a : Fin 12, ∑ b : Fin 12,
          (if a ≠ b ∧ key (v a) = key (v b) then 1 else 0) := Finset.sum_comm
    _ = ∑ v ∈ V, ∑ _a : Fin 12, 1 := by
        refine Finset.sum_congr rfl (fun v hv => Finset.sum_congr rfl (fun a _ => ?_))
        exact inner_count hcount v hv a
    _ = 12 * V.card := by simp [Finset.card_univ, mul_comm]

/-- **Main abstract count.**  Under the hypotheses, the total number of adjacent matched
pairs, summed over all admissible arrangements, equals the number of arrangements. -/
theorem sum_adjacent_matches
    (hinv : ∀ (ρ : Equiv.Perm (Fin 12)) (v : Fin 12 → α), v ∈ V → v ∘ ρ ∈ V)
    (hcount : ∀ v ∈ V, ∀ a : Fin 12,
      (univ.filter (fun b => key (v b) = key (v a))).card = 2) :
    ∑ v ∈ V, ∑ i : Fin 11, (if key (v i.castSucc) = key (v i.succ) then 1 else 0) = V.card := by
  set n := matchCount key V 0 1 with hn
  have hall : ∀ a b : Fin 12, a ≠ b → matchCount key V a b = n :=
    fun a b hab => matchCount_eq hinv hab (by decide)
  have h132 : ∑ a : Fin 12, ∑ b : Fin 12, (if a ≠ b then matchCount key V a b else 0)
      = 132 * n := by
    have : ∀ a b : Fin 12, (if a ≠ b then matchCount key V a b else 0)
        = (if a ≠ b then n else 0) := by
      intro a b
      by_cases hab : a = b
      · simp [hab]
      · rw [if_pos hab, if_pos hab, hall a b hab]
    simp only [this]
    have h11 : ∀ x : Fin 12, (∑ y : Fin 12, if x ≠ y then n else 0) = 11 * n := by
      intro x
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
        Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ x)]
      simp
    rw [Finset.sum_congr rfl (fun x _ => h11 x)]
    simp [Finset.card_univ]
    ring
  have hkey : 11 * n = V.card := by
    have := sum_matchCount (key := key) (V := V) hcount
    rw [h132] at this
    omega
  calc ∑ v ∈ V, ∑ i : Fin 11, (if key (v i.castSucc) = key (v i.succ) then 1 else 0)
      = ∑ i : Fin 11, ∑ v ∈ V, (if key (v i.castSucc) = key (v i.succ) then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ _i : Fin 11, n := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.card_filter]
        exact hall _ _ (Fin.ne_of_lt Fin.castSucc_lt_succ)
    _ = V.card := by simp [Finset.card_univ, hkey]

/-- The number of positions carrying a given value equals the count of that value in the
associated list. -/
lemma card_filter_eq_count {n : ℕ} {γ : Type*} [DecidableEq γ] [BEq γ] [LawfulBEq γ]
    (w : Fin n → γ) (r : γ) :
    (univ.filter (fun j => w j = r)).card = (List.ofFn w).count r := by
  rw [List.ofFn_eq_map, List.count_eq_length_filter, List.filter_map]
  simp only [List.length_map, Function.comp_def]
  rw [show (fun x => w x == r) = (fun x => decide (w x = r)) by
    funext x; by_cases h : w x = r <;> simp [h]]
  rfl

/-- Reindexing positions by a permutation does not change how often a value occurs. -/
lemma card_filter_comp {n : ℕ} {γ : Type*} [DecidableEq γ] (w : Fin n → γ)
    (ρ : Equiv.Perm (Fin n)) (r : γ) :
    (univ.filter (fun j => (w ∘ ρ) j = r)).card = (univ.filter (fun j => w j = r)).card := by
  refine Finset.card_bij' (fun j _ => ρ j) (fun j _ => ρ.symm j) ?_ ?_ ?_ ?_ <;>
    intro j hj <;> simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hj ⊢ <;>
    simp [hj]

/-- A list of length twelve is determined by its entries. -/
lemma ofFn_getElem {γ : Type*} [Inhabited γ] (l : List γ) (h : l.length = 12) :
    List.ofFn (fun j : Fin 12 => l[(j : ℕ)]!) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_ofFn, getElem!_pos]

end AdjacentPairs
