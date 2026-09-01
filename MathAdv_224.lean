import Mathlib

/-- Euler's totient function at a prime power: `φ(p^t) = p^t - p^(t-1)`
for `p` prime and `t` a positive integer.

The hypothesis `ht : 0 < t` is part of the statement as posed; note that in Lean's
truncated natural subtraction the identity happens to hold for `t = 0` as well,
so the proof does not need it. -/
theorem question_7 (p t : ℕ) (hp : Nat.Prime p) (ht : 0 < t) :
    Nat.totient (p ^ t) = p ^ t - p ^ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.totient_prime_pow hp (Nat.succ_pos s), Nat.mul_sub, mul_one, pow_succ,
    Nat.add_sub_cancel]
  simp
