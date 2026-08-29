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

/-- For a positive integer `k` and real `x` with `|x| < 1`,
`(1 - x)⁻ᵏ = ∑ₙ C(n+k-1, k-1) xⁿ`. -/
theorem bona_6
    (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : |x| < 1) :
    1 / (1 - x) ^ k
      = ∑' n : ℕ, (Nat.choose (n + k - 1) (k - 1) : ℝ) * x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hr : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) m hr
  rw [← this]
  simp

-- Multiple-choice question: the concept most relevant to this problem is
-- (a) the (generalized) binomial theorem.

#print axioms bona_6
