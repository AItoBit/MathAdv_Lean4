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

/-! # Climbing stairs with steps of size 1 or 2

`H n` is the number of ways of going up `n` stairs taking one or two steps at a time,
i.e. the number of lists of `1`s and `2`s summing to `n`.  We show `H 15 = 987` by
exhibiting a bijection between the set of such lists for `n = 15` and `Fin 987`.
-/

namespace Stairs

/-- The explicit list of all ways (recorded as lists of `1`s and `2`s) of climbing `n` stairs. -/
def stairs : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[1]]
  | (n + 2) => (stairs (n + 1)).map (fun s => 1 :: s) ++ (stairs n).map (fun s => 2 :: s)

/-- A list of `1`s and `2`s with sum `0` is empty. -/
theorem eq_nil_of_sum_zero (s : List ℕ) (h : ∀ a ∈ s, a = 1 ∨ a = 2) (hs : s.sum = 0) :
    s = [] := by
  cases s with
  | nil => rfl
  | cons a t =>
    exfalso
    have := h a (by simp)
    simp only [List.sum_cons] at hs
    omega

/-- Membership in `stairs n` characterises the lists of `1`s and `2`s summing to `n`. -/
theorem mem_stairs (n : ℕ) (s : List ℕ) :
    s ∈ stairs n ↔ ((∀ a ∈ s, a = 1 ∨ a = 2) ∧ s.sum = n) := by
  induction n using stairs.induct generalizing s with
  | case1 =>
    simp only [stairs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩; exact eq_nil_of_sum_zero s h1 h2
  | case2 =>
    simp only [stairs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩
      cases s with
      | nil => simp at h2
      | cons a t =>
        have ha := h1 a (by simp)
        simp only [List.sum_cons] at h2
        have hts : t.sum = 0 := by rcases ha with rfl | rfl <;> omega
        have htn : t = [] := eq_nil_of_sum_zero t (fun x hx => h1 x (by simp [hx])) hts
        subst htn
        simp only [List.sum_nil] at h2
        simp only [List.cons.injEq, and_true]
        omega
  | case3 n ih1 ih2 =>
    simp only [stairs, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [ih1] at ht
        refine ⟨?_, ?_⟩
        · rintro a (ha : a ∈ (1:ℕ) :: t)
          rcases List.mem_cons.mp ha with rfl | ha
          · left; rfl
          · exact ht.1 a ha
        · simp only [List.sum_cons, ht.2]; omega
      · rw [ih2] at ht
        refine ⟨?_, ?_⟩
        · rintro a (ha : a ∈ (2:ℕ) :: t)
          rcases List.mem_cons.mp ha with rfl | ha
          · right; rfl
          · exact ht.1 a ha
        · simp only [List.sum_cons, ht.2]; omega
    · rintro ⟨h1, h2⟩
      cases s with
      | nil => simp at h2
      | cons a t =>
        have ha := h1 a (by simp)
        have ht1 : ∀ x ∈ t, x = 1 ∨ x = 2 := fun x hx => h1 x (by simp [hx])
        simp only [List.sum_cons] at h2
        rcases ha with rfl | rfl
        · left; exact ⟨t, (ih1 t).mpr ⟨ht1, by omega⟩, rfl⟩
        · right; exact ⟨t, (ih2 t).mpr ⟨ht1, by omega⟩, rfl⟩

/-- The ways of climbing `n` stairs listed by `stairs n` are pairwise distinct. -/
theorem stairs_nodup (n : ℕ) : (stairs n).Nodup := by
  induction n using stairs.induct with
  | case1 => simp [stairs]
  | case2 => simp [stairs]
  | case3 n ih1 ih2 =>
    rw [stairs]
    refine List.Nodup.append ?_ ?_ ?_
    · exact ih1.map (fun a b h => by simpa using h)
    · exact ih2.map (fun a b h => by simpa using h)
    · rintro x hx hy
      simp only [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, hb⟩ := hy
      simp at hb

set_option maxRecDepth 100000 in
/-- There are exactly `987` ways of climbing `15` stairs: `H 15 = 987`. -/
theorem stairs_length_15 : (stairs 15).length = 987 := by rfl

end Stairs

/-- The set of ways of going up `15` stairs, taking one or two steps at a time (encoded as
the lists of `1`s and `2`s with sum `15`), is in bijection with `Fin 987`; i.e. `H 15 = 987`. -/
theorem Lovasz_13 :
  Nonempty ({ s : List ℕ // (∀ a ∈ s, a = 1 ∨ a = 2) ∧ s.sum = 15 } ≃ Fin 987) := by
  refine ⟨(Equiv.subtypeEquivRight (fun s => (Stairs.mem_stairs 15 s).symm)).trans ?_⟩
  exact (List.Nodup.getEquiv (Stairs.stairs 15) (Stairs.stairs_nodup 15)).symm.trans
    (finCongr Stairs.stairs_length_15)
