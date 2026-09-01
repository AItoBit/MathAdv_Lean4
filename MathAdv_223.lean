import Mathlib

/-- Teorema (number_theory_4_9, Q223 / question_6):
    Para todo entero positivo n, se cumple n < 3ⁿ (demostrado por inducción). -/
theorem question_6 (n : ℕ) (hn : 0 < n) :
    (n : ℕ) < 3^n := by
  induction n with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        decide
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        have ih' := ih hk_pos
        have h_pow_pos : 0 < 3^k := by positivity
        calc
          k + 1 < 3^k + 1 := Nat.add_lt_add_right ih' 1
          _ ≤ 3^k + 2 * 3^k := by omega
          _ = 3^(k + 1) := by
              have : 3^k + 2 * 3^k = 3 * 3^k := by ring
              rw [this]
              exact (pow_succ' 3 k).symm
