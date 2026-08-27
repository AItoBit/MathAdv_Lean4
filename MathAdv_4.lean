import Mathlib

open DihedralGroup

/-- Gallian 4.9 (#5): For every even integer `n ≥ 2`, `Dₙ` has a subgroup of order 4.
    The subgroup constructed is the Klein four-group `{1, r m, sr 0, sr m}` where `m = n / 2`. -/
theorem Gallian_5
    (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) :
    ∃ H : Subgroup (DihedralGroup n), Nonempty (↥H ≃ Fin 4) := by
  -- Instance needed to know DihedralGroup n (and thus any subtype) is Finite
  have : NeZero n := ⟨by omega⟩

  -- Write n = m + m with 1 ≤ m < n
  obtain ⟨m, hm⟩ := hn
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega

  -- In ZMod n: m + m = 0 and -m = m
  have ha : (m : ZMod n) + (m : ZMod n) = 0 := by
    have h : ((m + m : ℕ) : ZMod n) = 0 := by rw [← hm]; simp
    rwa [Nat.cast_add] at h
  have ha' : -(m : ZMod n) = (m : ZMod n) := neg_eq_of_add_eq_zero_left ha

  -- In ZMod n: m ≠ 0 because 0 < m < n
  have ha0 : (m : ZMod n) ≠ 0 := by
    intro h
    have hv : (m : ZMod n).val = m := ZMod.val_cast_of_lt hmn
    rw [h] at hv
    simp at hv
    omega

  -- Construct the Klein four-group V = {r 0, r m, sr 0, sr m} ≤ Dₙ
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (DihedralGroup n),
      (K : Set (DihedralGroup n)) = {r 0, r (m : ZMod n), sr 0, sr (m : ZMod n)} :=
    ⟨{ carrier := {r 0, r (m : ZMod n), sr 0, sr (m : ZMod n)}
       mul_mem' := by
         intro x y hx hy
         simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
         rcases hx with rfl | rfl | rfl | rfl <;>
           rcases hy with rfl | rfl | rfl | rfl <;> simp [ha, ha']
       one_mem' := Or.inl rfl        -- (1 : Dₙ) = r 0 definitionally
       inv_mem' := by
         intro x hx
         simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
         rcases hx with rfl | rfl | rfl | rfl <;> simp [ha'] }, rfl⟩

  -- Prove the 4 elements are pairwise distinct
  have hne : (0 : ZMod n) ≠ (m : ZMod n) := fun h => ha0 h.symm
  have h1 : (r 0 : DihedralGroup n) ∉
      ({r (m : ZMod n), sr 0, sr (m : ZMod n)} : Set (DihedralGroup n)) := by
    rintro (h | h | h)
    · injection h with h; exact hne h
    · contradiction
    · contradiction
  have h2 : (r (m : ZMod n) : DihedralGroup n) ∉
      ({sr 0, sr (m : ZMod n)} : Set (DihedralGroup n)) := by
    rintro (h | h) <;> contradiction
  have h3 : (sr 0 : DihedralGroup n) ≠ sr (m : ZMod n) := by
    intro h
    injection h with h
    exact hne h

  -- Compute the cardinality |K| = 4
  have e1 := Set.ncard_insert_of_notMem h1
  have e2 := Set.ncard_insert_of_notMem h2
  have e3 := Set.ncard_pair h3
  have hcard : Nat.card K = 4 := by
    have hcoe : Nat.card K = (K : Set (DihedralGroup n)).ncard := rfl
    rw [hcoe, hK, e1, e2, e3]

  -- Conclude the existence of the bijection with Fin 4
  exact ⟨K, ⟨Finite.equivFinOfCardEq hcard⟩⟩
