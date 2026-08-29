import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000

/-!
# Seating tourists at identical circular tables
-/

namespace Bona

/-- A seating arrangement of `n` tourists: everybody points at their left neighbour. -/
abbrev Seating (n : ℕ) := Equiv.Perm (Fin n)

/-- The number of tables seating **at least two** tourists (this is the original definition:
Mathlib's `cycleType` ignores fixed points). -/
def numTables {n : ℕ} (σ : Seating n) : ℕ :=
  Multiset.card σ.cycleType

/-- The number of tables, counting also the tables occupied by a single tourist. -/
def numAllTables {n : ℕ} (σ : Seating n) : ℕ :=
  Multiset.card σ.cycleType + (Finset.univ.filter (fun x : Fin n => σ x = x)).card

def ValidSeatings (n k : ℕ) : Type :=
  { σ : Seating n // numTables σ = k }

/-- The seatings of `n` tourists at exactly `k` identical circular tables. -/
def AllValidSeatings (n k : ℕ) : Type :=
  { σ : Seating n // numAllTables σ = k }

instance (n k : ℕ) : Fintype (ValidSeatings n k) :=
  inferInstanceAs (Fintype { σ : Seating n // numTables σ = k })

instance (n k : ℕ) : Fintype (AllValidSeatings n k) :=
  inferInstanceAs (Fintype { σ : Seating n // numAllTables σ = k })

/-- `H n k`, the number of ways to seat `n` tourists at `k` identical circular tables. -/
def H (n k : ℕ) : ℕ := Fintype.card (AllValidSeatings n k)

/-! ### The original statement is false -/

lemma card_cycleType_le (σ : Equiv.Perm (Fin 8)) : Multiset.card σ.cycleType ≤ 4 := by
  have h1 : Multiset.card σ.cycleType • 2 ≤ σ.cycleType.sum :=
    Multiset.card_nsmul_le_sum (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx)
  have h2 : σ.cycleType.sum ≤ Fintype.card (Fin 8) := Equiv.Perm.sum_cycleType_le σ
  simp only [Fintype.card_fin, smul_eq_mul] at h1 h2
  omega

instance : IsEmpty (ValidSeatings 8 6) := by
  constructor
  rintro ⟨σ, hσ⟩
  have := card_cycleType_le σ
  rw [numTables] at hσ
  omega

/-- The original statement `Nonempty (ValidSeatings 8 6 ≃ Fin 322)` is false, because
`ValidSeatings 8 6` is empty: `numTables` only counts the tables with at least two tourists,
and a permutation of eight elements has at most four such cycles. -/
theorem bona_8_original_false : ¬ Nonempty (ValidSeatings 8 6 ≃ Fin 322) := by
  rintro ⟨e⟩
  exact IsEmpty.false (e.symm ⟨0, by norm_num⟩)

/-! ### The corrected statement -/

/-- A multiset of cycle lengths (all at least `2`) whose sum exceeds its cardinality by `2`
is either `{3}` or `{2, 2}`. -/
lemma multiset_classification {m : Multiset ℕ} (h2 : ∀ a ∈ m, 2 ≤ a)
    (hsum : m.sum = Multiset.card m + 2) : m = {3} ∨ m = {2, 2} := by
  have h1 : Multiset.card m • 2 ≤ m.sum := Multiset.card_nsmul_le_sum h2
  simp only [smul_eq_mul] at h1
  have hc : Multiset.card m ≤ 2 := by omega
  interval_cases h : Multiset.card m
  · simp_all [Multiset.card_eq_zero.mp h]
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h
    simp_all
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    have hA : a = 2 := by omega
    have hB : b = 2 := by omega
    subst hA; subst hB
    right; rfl

lemma numAllTables_eq (σ : Equiv.Perm (Fin 8)) :
    numAllTables σ = Multiset.card σ.cycleType + (8 - σ.cycleType.sum) := by
  show Multiset.card σ.cycleType + (Finset.univ.filter (fun x : Fin 8 => σ x = x)).card = _
  have hset : (Finset.univ.filter (fun x : Fin 8 => σ x = x)) = Finset.univ \ σ.support := by
    ext x; simp [Equiv.Perm.mem_support]
  rw [hset, Finset.card_sdiff, Equiv.Perm.sum_cycleType]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.inter_eq_left.mpr (Finset.subset_univ _)]

/-- Eight tourists sit at six tables exactly when the permutation has a single `3`-cycle
(and five fixed points) or two `2`-cycles (and four fixed points). -/
lemma filter_eq_union :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => numAllTables σ = 6)) =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {3})) ∪
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {2, 2})) := by
  ext σ
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, numAllTables_eq]
  constructor
  · intro h
    have h2 : ∀ a ∈ σ.cycleType, 2 ≤ a := fun _ ha =>
      Equiv.Perm.two_le_of_mem_cycleType ha
    have hle : σ.cycleType.sum ≤ 8 := by
      simpa using Equiv.Perm.sum_cycleType_le σ
    have hcard : Multiset.card σ.cycleType • 2 ≤ σ.cycleType.sum :=
      Multiset.card_nsmul_le_sum h2
    simp only [smul_eq_mul] at hcard
    have hsum_eq : σ.cycleType.sum = Multiset.card σ.cycleType + 2 := by omega
    exact multiset_classification h2 hsum_eq
  · rintro (h | h)
    · rw [h]
      decide
    · rw [h]
      decide

/-- There are `112` permutations of eight elements consisting of a single `3`-cycle. -/
lemma card_cycleType_three :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {3})).card = 112 := by
  have h := Equiv.Perm.card_of_cycleType (Fin 8) {3}
  revert h
  decide

/-- There are `210` permutations of eight elements consisting of two disjoint `2`-cycles. -/
lemma card_cycleType_two_two :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {2, 2})).card = 210 := by
  have h := Equiv.Perm.card_of_cycleType (Fin 8) {2, 2}
  revert h
  decide

/-- `H (8, 6) = 322`: there are `322` ways to seat `8` tourists at `6` identical circular
tables. -/
theorem H_8_6 : H 8 6 = 322 := by
  have hcard : Fintype.card (AllValidSeatings 8 6)
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => numAllTables σ = 6)).card :=
    Fintype.card_subtype _
  have hdisj :
      Disjoint (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {3}))
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {2, 2})) := by
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by decide)
  rw [H, hcard, filter_eq_union, Finset.card_union_of_disjoint hdisj, card_cycleType_three,
    card_cycleType_two_two]

/-- The corrected version of the original statement: the seatings of `8` tourists at `6`
identical circular tables are in bijection with `Fin 322`. -/
theorem bona_8 : Nonempty (AllValidSeatings 8 6 ≃ Fin 322) :=
  ⟨Fintype.equivFinOfCardEq H_8_6⟩

end Bona
