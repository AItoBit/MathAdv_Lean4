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

/-!
# Order of a power of a group element

If `a` is an element of a group `G` with `orderOf a = n` and `k` is a positive integer,
then `|a ^ k| = n / gcd (n, k)`.

Note on the statement: the hypothesis `0 < k` is genuinely needed. If `a` has infinite
order (`orderOf a = 0` in Lean's convention) and `k = 0`, then `a ^ k = 1` has order `1`,
while `n / Nat.gcd n k = 0 / 0 = 0`. The original statement without `0 < k` is therefore
false in that degenerate case; see `Gallian_3_counterexample_k_zero` below.
-/

/- Original statement (false as stated, because of the case `orderOf a = 0`, `k = 0`):

theorem Gallian_3
    {G : Type*} [Group G] (a : G) (n k : ℕ)
    (hord : orderOf a = n) :
    orderOf (a ^ k) = n / Nat.gcd n k := by
  sorry
-/

/-- **Order of a power.** For `a` in a group `G` of order `n = orderOf a` and `k > 0`,
the order of `a ^ k` is `n / gcd (n, k)`. -/
theorem Gallian_3
    {G : Type*} [Group G] (a : G) (n k : ℕ)
    (hord : orderOf a = n) (hk : 0 < k) :
    orderOf (a ^ k) = n / Nat.gcd n k := by
  subst hord
  exact orderOf_pow' a hk.ne'

/-- Without the hypothesis `0 < k` the statement fails: take `a = 1` in `ℤ` (additively,
an element of infinite order) and `k = 0`. -/
theorem Gallian_3_counterexample_k_zero :
    ∃ (a : Multiplicative ℤ) (n k : ℕ),
      orderOf a = n ∧ orderOf (a ^ k) ≠ n / Nat.gcd n k := by
  refine ⟨Multiplicative.ofAdd 1, 0, 0, ?_, ?_⟩
  · simp [isOfFinAddOrder_iff_nsmul_eq_zero]
  · simp
