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
## Euler's totient function via the prime factorization

If `n = p₁^α₁ ⋯ p_s^α_s` with the `pᵢ` distinct primes and `αᵢ ≥ 1`, then
`φ(n) = n ∏ (1 - 1/pᵢ)`.

Multiple-choice question: the answer is (b), the inclusion-exclusion principle (counting the
integers in `[1, n]` divisible by none of the `pᵢ`).  The proof formalized here instead uses
multiplicativity of `φ` over coprime factors together with `φ(p^a) = p^(a-1)(p-1)`.
-/

/-- The totient function is multiplicative over a finite family of pairwise coprime numbers. -/
theorem Nat.totient_prod_of_pairwise_coprime {ι : Type*} (t : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (f i) (f j)) :
    Nat.totient (∏ i ∈ t, f i) = ∏ i ∈ t, Nat.totient (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      rw [Nat.totient_mul]
      · rw [ih]
        intro i hi j hj hij
        exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      · refine Nat.Coprime.prod_right ?_
        intro i hi
        exact h x (Finset.mem_insert_self x t) i (Finset.mem_insert_of_mem hi)
          (fun he => hx (he ▸ hi))

/-- For a prime `p` and `a ≥ 1`, `φ(p^a) = p^a (1 - 1/p)` as rationals. -/
theorem Nat.totient_prime_pow_rat {p a : ℕ} (hp : Nat.Prime p) (ha : 0 < a) :
    (Nat.totient (p ^ a) : ℚ) = (p : ℚ) ^ a * (1 - 1 / (p : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.pos hp).ne'
  have hp1 : 1 ≤ p := hp.one_lt.le
  rw [Nat.totient_prime_pow hp ha]
  push_cast [Nat.cast_sub hp1, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr ha.ne')]
  field_simp
  have hpa : (p : ℚ) ^ (a - 1) * (p : ℚ) = (p : ℚ) ^ a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpa]
  ring

/-!
The statement below is the requested one, with the (necessary) extra hypothesis that every
exponent `a i` is positive.  Without it the claim is false: e.g. for `s = 1`, `p 0 = 2`,
`a 0 = 0` the left-hand side is `φ(1) = 1` while the right-hand side is `1 * (1 - 1/2) = 1/2`.
The original statement is kept, commented out, below.
-/
theorem Lovasz_14
    (s : ℕ) (p a : Fin s → ℕ)
    (hprime : ∀ i, Nat.Prime (p i))
    (hpos : ∀ i, 0 < a i)
    (hcop   : ∀ {i j : Fin s}, i ≠ j → Nat.Coprime (p i) (p j)) :
    (Nat.totient (∏ i : Fin s, (p i) ^ (a i)) : ℚ)
      = (∏ i : Fin s, (p i) ^ (a i) : ℚ)
        * ∏ i : Fin s, (1 - 1 / (p i : ℚ)) := by
  rw [Nat.totient_prod_of_pairwise_coprime _ _
    (fun i _ j _ hij => Nat.Coprime.pow _ _ (hcop hij))]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    simpa using Nat.totient_prime_pow_rat (hprime i) (hpos i)

/-
Original (false without `0 < a i`) statement:

theorem Lovasz_14'
    (s : ℕ) (p a : Fin s → ℕ)
    (hprime : ∀ i, Nat.Prime (p i))
    (hcop   : ∀ {i j : Fin s}, i ≠ j → Nat.Coprime (p i) (p j)) :
    (Nat.totient (∏ i : Fin s, (p i) ^ (a i)) : ℚ)
      = (∏ i : Fin s, (p i) ^ (a i) : ℚ)
        * ∏ i : Fin s, (1 - 1 / (p i : ℚ)) := by
  sorry
-/

/-- The original statement (without positivity of the exponents) is false. -/
theorem Lovasz_14_counterexample :
    ¬ (∀ (s : ℕ) (p a : Fin s → ℕ), (∀ i, Nat.Prime (p i)) →
        (∀ {i j : Fin s}, i ≠ j → Nat.Coprime (p i) (p j)) →
        (Nat.totient (∏ i : Fin s, (p i) ^ (a i)) : ℚ)
          = (∏ i : Fin s, (p i) ^ (a i) : ℚ) * ∏ i : Fin s, (1 - 1 / (p i : ℚ))) := by
  intro h
  have := h 1 (fun _ => 2) (fun _ => 0) (fun _ => Nat.prime_two)
    (fun {i j} hij => absurd (Subsingleton.elim i j) hij)
  norm_num at this
