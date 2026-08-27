import Mathlib

/-- Let `x` be an element of a cyclic group of order `15`. If exactly two of the elements
`x ^ 3`, `x ^ 5`, `x ^ 9` are equal, then the order of `x ^ 13` is `3`.

The proof uses Lagrange's theorem: `orderOf x ∣ Fintype.card G = 15`. -/
theorem Gallian_1
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (x : G) (hG : Fintype.card G = 15)
    (h :
        (x ^ 3 = x ^ 5 ∧ x ^ 3 ≠ x ^ 9) ∨
        (x ^ 3 = x ^ 9 ∧ x ^ 3 ≠ x ^ 5) ∨
        (x ^ 5 = x ^ 9 ∧ x ^ 5 ≠ x ^ 3)) :
    orderOf (x ^ 13) = 3 := by
  -- Lagrange's theorem
  have hdvd : orderOf x ∣ 15 := hG ▸ orderOf_dvd_card
  have hcancel : ∀ a b : ℕ, x ^ a = x ^ (a + b) → x ^ b = 1 := by
    intro a b hab
    have : x ^ a * x ^ b = x ^ a * 1 := by rw [mul_one, ← pow_add]; exact hab.symm
    exact mul_left_cancel this
  have key : orderOf x = 3 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have h2' : x ^ 2 = 1 := hcancel 3 2 (by simpa using h1)
      have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
      have : orderOf x ∣ 1 := Nat.dvd_gcd hd2 hdvd
      have hx : x = 1 := by
        rw [← orderOf_eq_one_iff]
        exact Nat.dvd_one.mp this
      exact h2 (by rw [hx]; simp)
    · have h6 : x ^ 6 = 1 := hcancel 3 6 (by simpa using h1)
      have hd6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
      have hd3 : orderOf x ∣ 3 := Nat.dvd_gcd hd6 hdvd
      have hne : orderOf x ≠ 1 := by
        intro he
        have hx : x = 1 := orderOf_eq_one_iff.mp he
        exact h2 (by rw [hx]; simp)
      exact (Nat.prime_three.eq_one_or_self_of_dvd _ hd3).resolve_left hne
    · exfalso
      have h4 : x ^ 4 = 1 := hcancel 5 4 (by simpa using h1)
      have hd4 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have : orderOf x ∣ 1 := Nat.dvd_gcd hd4 hdvd
      have hx : x = 1 := by
        rw [← orderOf_eq_one_iff]
        exact Nat.dvd_one.mp this
      exact h2 (by rw [hx]; simp)
  have hx3 : x ^ 3 = 1 := by rw [← key]; exact pow_orderOf_eq_one x
  have : x ^ 13 = x := by
    calc x ^ 13 = (x ^ 3) ^ 4 * x := by rw [← pow_mul, ← pow_succ]
    _ = x := by rw [hx3, one_pow, one_mul]
  rw [this, key]
