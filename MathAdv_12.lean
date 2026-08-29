import Mathlib

/-!
# Nilpotent elements and units

Let `a` be an element of a ring `R` with unity such that `a ^ n = 0` for some positive
integer `n`. Then `1 - a` has a two-sided multiplicative inverse in `R`, namely the
finite geometric sum `b = 1 + a + a ^ 2 + ⋯ + a ^ (n - 1)`.
-/

/-- The candidate inverse of `1 - a`: the truncated geometric series `∑_{i<n} a^i`. -/
def geomInv {R : Type*} [Ring R] (a : R) (n : ℕ) : R := ∑ i ∈ Finset.range n, a ^ i

theorem geomInv_mul_one_sub {R : Type*} [Ring R] (a : R) (n : ℕ) (ha : a ^ n = 0) :
    geomInv a n * (1 - a) = 1 := by
  rw [geomInv, geom_sum_mul_neg, ha, sub_zero]

theorem one_sub_mul_geomInv {R : Type*} [Ring R] (a : R) (n : ℕ) (ha : a ^ n = 0) :
    (1 - a) * geomInv a n = 1 := by
  rw [geomInv, mul_neg_geom_sum, ha, sub_zero]

/-- If `a ^ n = 0` for some positive integer `n`, then `1 - a` is invertible in `R`. -/
theorem Gallian_13
    (R : Type*) [Ring R] (a : R)
    (h : ∃ n : ℕ, 0 < n ∧ a ^ n = 0) :
    ∃ b : R, (1 - a) * b = 1 ∧ b * (1 - a) = 1 := by
  obtain ⟨n, -, ha⟩ := h
  exact ⟨geomInv a n, one_sub_mul_geomInv a n ha, geomInv_mul_one_sub a n ha⟩
