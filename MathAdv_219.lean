import Mathlib

/-- Teorema (number_theory_4_9, Q219 / question_2):
    Si p > 0 y tanto p como p² + 2 son primos, entonces p = 3. -/
theorem question_2 (p : ℕ) (hp : 0 < p)
    (h1 : Nat.Prime p) (h2 : Nat.Prime (p^2 + 2)) :
    p = 3 := by
  have hmod := Nat.mod_lt p (by decide : 0 < 3)
  interval_cases h_rem : p % 3
  · -- Caso p % 3 = 0: 3 divide a p. Como p es primo, p = 3.
    have h3_dvd_p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h_rem
    exact (Nat.Prime.dvd_iff_eq h1 (by decide : 3 ≠ 1)).mp h3_dvd_p

  · -- Caso p % 3 = 1: p² + 2 es divisible por 3
    have h_div : 3 ∣ p^2 + 2 := by
      obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, (Nat.div_add_mod p 3).symm.trans (by rw [h_rem])⟩
      use 3 * k^2 + 2 * k + 1
      rw [hk]
      ring

    -- Pero p ≥ 2 implica p² + 2 ≥ 6 > 3, contradiciendo que p² + 2 sea primo
    have hp_ge : 2 ≤ p := Nat.Prime.two_le h1
    have h_gt3 : 3 < p^2 + 2 := by
      nlinarith
    have h_eq3 := (Nat.Prime.dvd_iff_eq h2 (by decide : 3 ≠ 1)).mp h_div
    omega

  · -- Caso p % 3 = 2: p² + 2 es divisible por 3
    have h_div : 3 ∣ p^2 + 2 := by
      obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, (Nat.div_add_mod p 3).symm.trans (by rw [h_rem])⟩
      use 3 * k^2 + 4 * k + 2
      rw [hk]
      ring

    have hp_ge : 2 ≤ p := Nat.Prime.two_le h1
    have h_gt3 : 3 < p^2 + 2 := by
      nlinarith
    have h_eq3 := (Nat.Prime.dvd_iff_eq h2 (by decide : 3 ≠ 1)).mp h_div
    omega
