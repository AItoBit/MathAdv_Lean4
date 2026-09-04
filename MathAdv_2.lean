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

/-- **Gallian 4.9.** If `a` is an element of a group `G` of order `n` and `k` is a positive
integer, then `|a^k| = n / gcd(n, k)`.

Note: the hypothesis `0 < k` (present in the informal statement) is genuinely needed; see
`Gallian_3_needs_k_pos` below for a counterexample when `k = 0` and `a` has infinite order
(`n = 0`).  For `n = 0` and `k > 0` the identity reads `0 = 0 / k`, which is correct. -/
theorem Gallian_3
    {G : Type*} [Group G] (a : G) (n k : ℕ) (hk : 0 < k)
    (hord : orderOf a = n) :
    orderOf (a ^ k) = n / Nat.gcd n k := by
  subst hord
  exact orderOf_pow' a hk.ne'

/-- The hypothesis `0 < k` cannot be dropped from `Gallian_3`: for an element of infinite
order (`n = 0`) and `k = 0` we get `orderOf (a ^ 0) = 1` while `n / gcd (n, k) = 0`. -/
theorem Gallian_3_needs_k_pos :
    ¬ ∀ (G : Type) (_ : Group G) (a : G) (n k : ℕ),
        orderOf a = n → orderOf (a ^ k) = n / Nat.gcd n k := by
  intro h
  have ha : orderOf (Multiplicative.ofAdd (1 : ℤ)) = 0 := by
    simp [isOfFinAddOrder_iff_nsmul_eq_zero]
  have := h (Multiplicative ℤ) inferInstance (Multiplicative.ofAdd (1 : ℤ)) 0 0 ha
  simp at this
