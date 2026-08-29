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

set_option grind.warning false

/-- `n` is a perfect cube. -/
def IsCube (n : ℕ) : Prop := ∃ m : ℕ, m ^ 3 = n

/-- `n` has no prime divisor larger than `10`. -/
def TenSmooth (n : ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, Nat.Prime p → p ∣ n → p ≤ 10

/-- A positive natural number all of whose prime exponents are divisible by `3`
is a perfect cube. -/
theorem isCube_of_three_dvd_factorization {n : ℕ} (hn : n ≠ 0)
    (H : ∀ p, 3 ∣ n.factorization p) : IsCube n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 3), ?_⟩
  rw [← Finset.prod_pow]
  have h1 : ∀ p ∈ n.primeFactors, (p ^ (n.factorization p / 3)) ^ 3
      = p ^ (n.factorization p) := by
    intro p _
    rw [← pow_mul, Nat.div_mul_cancel (H p)]
  rw [Finset.prod_congr rfl h1]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- The four primes that can divide a `10`-smooth number. -/
def smallPrimes : Fin 4 → ℕ := ![2, 3, 5, 7]

/-- A prime that is at most `10` is one of `2, 3, 5, 7`. -/
theorem exists_index_of_prime_le_ten {p : ℕ} (hp : Nat.Prime p) (hle : p ≤ 10) :
    ∃ t : Fin 4, smallPrimes t = p := by
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact absurd hp (by decide)
  · exact ⟨2, rfl⟩
  · exact absurd hp (by decide)
  · exact ⟨3, rfl⟩
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

/-- The exponent vector, mod `3`, of a number at the primes `2, 3, 5, 7`. -/
def cubeClass (n : ℕ) : Fin 4 → ZMod 3 :=
  fun t => ((n.factorization (smallPrimes t) : ℕ) : ZMod 3)

/-- If three positive `10`-smooth numbers have the same exponent vector mod `3`,
their product is a perfect cube. -/
theorem isCube_mul_of_cubeClass_eq {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxs : TenSmooth x) (hys : TenSmooth y) (hzs : TenSmooth z)
    (hxy : cubeClass x = cubeClass y) (hxz : cubeClass x = cubeClass z) :
    IsCube (x * y * z) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  have hz0 : z ≠ 0 := hz.ne'
  refine isCube_of_three_dvd_factorization (by positivity) ?_
  intro p
  rw [Nat.factorization_mul (Nat.mul_ne_zero hx0 hy0) hz0,
    Nat.factorization_mul hx0 hy0]
  simp only [Finsupp.coe_add, Pi.add_apply]
  by_cases hp : Nat.Prime p
  · by_cases hple : p ≤ 10
    · obtain ⟨t, rfl⟩ := exists_index_of_prime_le_ten hp hple
      have h1 := congrFun hxy t
      have h2 := congrFun hxz t
      simp only [cubeClass] at h1 h2
      have hzero : ((x.factorization (smallPrimes t) + y.factorization (smallPrimes t)
          + z.factorization (smallPrimes t) : ℕ) : ZMod 3) = 0 := by
        push_cast
        rw [← h1, ← h2]
        have h3 : ((x.factorization (smallPrimes t) : ℕ) : ZMod 3)
            + ((x.factorization (smallPrimes t) : ℕ) : ZMod 3)
            + ((x.factorization (smallPrimes t) : ℕ) : ZMod 3)
            = 3 * ((x.factorization (smallPrimes t) : ℕ) : ZMod 3) := by ring
        rw [h3, show (3 : ZMod 3) = 0 from rfl, zero_mul]
      exact (ZMod.natCast_eq_zero_iff _ 3).mp hzero
    · have hx1 : x.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hple (hxs hp hd))
      have hy1 : y.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hple (hys hp hd))
      have hz1 : z.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hple (hzs hp hd))
      simp [hx1, hy1, hz1]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Main theorem.** Among any 175 positive integers with no prime divisor
larger than 10, there are three whose product is a perfect cube. -/
theorem bona_3
    (a : Fin 175 → ℕ)
    (hpos : ∀ i, 0 < a i)
    (hsmooth : ∀ i, TenSmooth (a i)) :
    ∃ i j k : Fin 175,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ IsCube (a i * a j * a k) := by
  -- Pigeonhole: 175 numbers, only 3^4 = 81 possible exponent vectors mod 3.
  have hcard : Fintype.card (Fin 4 → ZMod 3) * 2 < Fintype.card (Fin 175) := by
    simp
  obtain ⟨v, hv⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (fun i : Fin 175 => cubeClass (a i)) hcard
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  exact ⟨i, j, k, hij, hik, hjk,
    isCube_mul_of_cubeClass_eq (hpos i) (hpos j) (hpos k) (hsmooth i) (hsmooth j) (hsmooth k)
      (hi.trans hj.symm) (hi.trans hk.symm)⟩

/-- The answer to the multiple-choice question: the pigeonhole principle. -/
def bona_3_answer : String := "(c) Pigeonhole principle"
