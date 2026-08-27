import Mathlib

/-!
# Gallian 4.9 (#4): `Dₙ` has a subgroup of order `4` ⟺ `n` is even

In Mathlib, `DihedralGroup n` is the group of order `2n` with elements
`r i` (rotations) and `sr i` (reflections), `i : ZMod n`, and

  `r i * r j = r (i + j)`,   `r i * sr j = sr (j - i)`,
  `sr i * r j = sr (i + j)`, `sr i * sr j = r (j - i)`,   `1 = r 0`.
-/

open DihedralGroup in
theorem Gallian_4
    (n : ℕ) (hn : 3 ≤ n) :
    (∃ H : Subgroup (DihedralGroup n), Nonempty (↥H ≃ Fin 4)) ↔ Even n := by
  have : NeZero n := ⟨by omega⟩
  have hG : Nat.card (DihedralGroup n) = 2 * n := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  constructor
  · ---------------------------------------------------------------- (⇒)
    -- Lagrange: `4 = |H|` divides `|Dₙ| = 2n`, so `n` is even.
    rintro ⟨H, ⟨e⟩⟩
    have hH : Nat.card H = 4 := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hdvd : Nat.card H ∣ Nat.card (DihedralGroup n) :=
      ⟨H.index, (H.card_mul_index).symm⟩
    rw [hH, hG] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by omega⟩
  · ---------------------------------------------------------------- (⇐)
    -- The Klein four-group `{1, r m, sr 0, sr m}`, `m = n/2`.
    rintro ⟨m, hm⟩
    have hm2 : 2 ≤ m := by omega
    -- `m + m = 0` in `ZMod n`, because `m + m = n`.
    have ha : (m : ZMod n) + (m : ZMod n) = 0 := by
      have h : ((m + m : ℕ) : ZMod n) = 0 := by rw [← hm]; simp
      rwa [Nat.cast_add] at h
    have ha' : -(m : ZMod n) = (m : ZMod n) := neg_eq_of_add_eq_zero_left ha
    -- `m ≠ 0` in `ZMod n`, because `0 < m < n`.
    have ha0 : (m : ZMod n) ≠ 0 := by
      intro h
      have hv : (m : ZMod n).val = m := ZMod.val_cast_of_lt (by omega)
      rw [h] at hv
      simp at hv
      omega
    -- The subgroup itself: closure under `*` and `⁻¹` is 16 + 4 rewrites.
    obtain ⟨K, hK⟩ : ∃ K : Subgroup (DihedralGroup n),
        (K : Set (DihedralGroup n)) = {r 0, r (m : ZMod n), sr 0, sr (m : ZMod n)} :=
      ⟨{ carrier := {r 0, r (m : ZMod n), sr 0, sr (m : ZMod n)}
         mul_mem' := by
           intro x y hx hy
           simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
           rcases hx with rfl | rfl | rfl | rfl <;>
             rcases hy with rfl | rfl | rfl | rfl <;> simp [ha, ha']
         one_mem' := Or.inl rfl        -- `(1 : Dₙ) = r 0` definitionally
         inv_mem' := by
           intro x hx
           simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
           rcases hx with rfl | rfl | rfl | rfl <;> simp [ha'] }, rfl⟩
    refine ⟨K, ⟨Finite.equivFinOfCardEq ?_⟩⟩
    -- The four listed elements are pairwise distinct, hence `|K| = 4`.
    have hne : (0 : ZMod n) ≠ (m : ZMod n) := fun h => ha0 h.symm
    have h1 : (r 0 : DihedralGroup n) ∉
        ({r (m : ZMod n), sr 0, sr (m : ZMod n)} : Set (DihedralGroup n)) := by
      rintro (h | h | h)
      · injection h with h
        exact hne h
      · contradiction
      · contradiction
    have h2 : (r (m : ZMod n) : DihedralGroup n) ∉
        ({sr 0, sr (m : ZMod n)} : Set (DihedralGroup n)) := by
      rintro (h | h) <;> contradiction
    have h3 : (sr 0 : DihedralGroup n) ≠ sr (m : ZMod n) := by
      intro h
      injection h with h
      exact hne h
    have e1 := Set.ncard_insert_of_notMem h1
    have e2 := Set.ncard_insert_of_notMem h2
    have e3 := Set.ncard_pair h3
    have hcoe : Nat.card K = (K : Set (DihedralGroup n)).ncard := rfl
    rw [hcoe, hK, e1, e2, e3]
