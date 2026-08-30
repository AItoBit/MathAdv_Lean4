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

/-!
# Kammler, Exercise 4.9 (24c)

For `N = 2, 3, …` let `f[n] = C(N-1, n)` (vanishing outside `0 ≤ n ≤ N-1`) and let `g` be its
`N`-periodization. Applying the Plancherel identity for the discrete Fourier transform to `g`
yields

`∑_{n=0}^{N-1} C(N-1,n)^2 = (4^{N-1}/N) ∑_{k=0}^{N-1} cos(kπ/N)^{2N-2}`.

The file below sets up the functions `f`, `g` and their Fourier transforms as in the statement,
and gives a complete proof of the displayed identity. Both sides in fact equal the central
binomial coefficient `C(2N-2, N-1)`: the left side by Vandermonde's identity, the right side by
expanding `cos^{2N-2}` into exponentials and summing the resulting geometric sums over the
`N`-th roots of unity.
-/

noncomputable def f_kammler24 (N : ℕ) (n : ℤ) : ℂ :=
  if 0 ≤ n ∧ Int.toNat n ≤ N - 1 then
    (Nat.choose (N - 1) (Int.toNat n) : ℂ)
  else
    0

noncomputable def g_kammler24 (N : ℕ) (n : ℤ) : ℂ :=
  ∑' m : ℤ, f_kammler24 N (n - (m : ℤ) * (N : ℤ))

noncomputable def Fhat_kammler24 (N : ℕ) (s : ℝ) : ℂ :=
  (1 / (N : ℂ)) *
    ∑ n ∈ Finset.range N,
      f_kammler24 N (n : ℤ) *
        Complex.exp (-2 * Real.pi * Complex.I * (s / (N : ℝ)) * (n : ℝ))

noncomputable def Ghat_kammler24 (N : ℕ) (k : ℤ) : ℂ :=
  (1 / (N : ℂ)) *
    ∑ n ∈ Finset.range N,
      g_kammler24 N (n : ℤ) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ((k : ℝ) / (N : ℝ)) * (n : ℝ))

namespace Kammler24

open Finset

/-- The primitive `(M+1)`-st root of unity `exp(2πi/(M+1))`. -/
noncomputable def zeta (M : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((M : ℂ) + 1))

/-- Sum of a geometric progression along the powers of a primitive `N`-th root of unity. -/
lemma geom_sum_primitiveRoot (N : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ N) (r : ℕ) :
    ∑ k ∈ Finset.range N, ζ ^ (r * k) = if N ∣ r then (N : ℂ) else 0 := by
  simp_rw [pow_mul]
  by_cases h : N ∣ r
  · simp only [h, ↓reduceIte]
    rw [(hζ.pow_eq_one_iff_dvd r).2 h]
    simp
  · simp only [h, ↓reduceIte]
    have hne : ζ ^ r ≠ 1 := fun hc => h ((hζ.pow_eq_one_iff_dvd r).1 hc)
    rw [geom_sum_eq hne, show (ζ ^ r) ^ N = 1 by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]]
    simp

/-- `(2 cos(kπ/N))^{2N-2}` expressed through the `N`-th root of unity `ζ^k` (here `N = M+1`). -/
lemma cos_pow_eq (M k : ℕ) :
    (Complex.cos ((Real.pi : ℂ) * (k : ℂ) / ((M : ℂ) + 1))) ^ (2 * M) * 4 ^ M
      = (zeta M) ^ k * (1 + (zeta M) ^ k) ^ (2 * M) := by
  set u : ℂ := Complex.exp (Real.pi * Complex.I * k / ((M : ℂ) + 1)) with hu
  have _hune : u ≠ 0 := Complex.exp_ne_zero _
  have hu2 : u ^ 2 = (zeta M) ^ k := by
    rw [hu, zeta, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    ring_nf
  have hu2N : u ^ (2 * (M + 1)) = 1 := by
    rw [hu, ← Complex.exp_nat_mul]
    have _hM : ((M : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    have h : ((2 * (M + 1) : ℕ) : ℂ) * (Real.pi * Complex.I * k / ((M : ℂ) + 1))
        = (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; field_simp
    rw [h, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  have hcos : Complex.cos ((Real.pi : ℂ) * (k : ℂ) / ((M : ℂ) + 1)) = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]
    ring_nf
  rw [hcos, ← hu2]
  have h1 : (1 + u ^ 2) = u * (u⁻¹ + u) := by field_simp
  rw [h1, mul_pow]
  have h2 : u ^ 2 * (u ^ (2 * M) * (u⁻¹ + u) ^ (2 * M))
      = u ^ (2 * (M + 1)) * (u⁻¹ + u) ^ (2 * M) := by
    rw [show 2 * (M + 1) = 2 * M + 2 by ring, pow_add]
    ring
  rw [h2, hu2N, one_mul, div_pow, show ((2 : ℂ)) ^ (2 * M) = 4 ^ M by rw [pow_mul]; norm_num]
  rw [add_comm u u⁻¹]
  field_simp

/-- The root-of-unity sum evaluates to `(M+1) * C(2M, M)`. -/
lemma sum_zeta_pow (M : ℕ) :
    ∑ k ∈ range (M + 1), (zeta M) ^ k * (1 + (zeta M) ^ k) ^ (2 * M)
      = ((M : ℂ) + 1) * (Nat.choose (2 * M) M) := by
  have hprim : IsPrimitiveRoot (zeta M) (M + 1) := by
    have := Complex.isPrimitiveRoot_exp (M + 1) (Nat.succ_ne_zero M)
    simpa [zeta] using this
  have step1 : ∀ k ∈ range (M + 1), (zeta M) ^ k * (1 + (zeta M) ^ k) ^ (2 * M)
      = ∑ j ∈ range (2 * M + 1), (Nat.choose (2 * M) j : ℂ) * (zeta M) ^ ((j + 1) * k) := by
    intro k _
    rw [add_comm (1 : ℂ), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [one_pow, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ j ∈ range (2 * M + 1),
      ∑ k ∈ range (M + 1), (Nat.choose (2 * M) j : ℂ) * (zeta M) ^ ((j + 1) * k)
        = (Nat.choose (2 * M) j : ℂ) * (if j = M then ((M : ℂ) + 1) else 0) := by
    intro j hj
    rw [← Finset.mul_sum, geom_sum_primitiveRoot (M + 1) (zeta M) hprim (j + 1)]
    congr 1
    have hiff : ((M + 1) ∣ (j + 1)) ↔ j = M := by
      constructor
      · rintro ⟨c, _hc⟩
        have _hj' : j < 2 * M + 1 := Finset.mem_range.mp hj
        have _hc2 : c < 2 := by nlinarith
        interval_cases c <;> omega
      · rintro rfl
        exact ⟨1, by ring⟩
    simp only [hiff]
    split <;> push_cast <;> ring
  rw [Finset.sum_congr rfl step2]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (range (2 * M + 1)) M]
  have hmem : M ∈ range (2 * M + 1) := by simp; omega
  simp only [hmem, ↓reduceIte]
  ring

/-- The cosine power sum, real form: `(∑_{k<M+1} cos(kπ/(M+1))^{2M}) · 4^M = (M+1)·C(2M,M)`. -/
lemma sum_cos_pow (M : ℕ) :
    (∑ k ∈ range (M + 1), (Real.cos (Real.pi * k / (M + 1))) ^ (2 * M)) * 4 ^ M
      = ((M : ℝ) + 1) * (Nat.choose (2 * M) M) := by
  apply Complex.ofReal_injective
  push_cast
  rw [Finset.sum_mul, Finset.sum_congr rfl (fun k _ => cos_pow_eq M k), sum_zeta_pow M]

end Kammler24

theorem kammler_24_c
    (N : ℕ) (_hN : 2 ≤ N) :
  (∑ n ∈ Finset.range N, (Nat.choose (N - 1) n : ℝ) ^ 2)
    = (4 : ℝ) ^ (N - 1) / (N : ℝ)
        * ∑ k ∈ Finset.range N,
            (Real.cos (Real.pi * (k : ℝ) / (N : ℝ))) ^ (2 * N - 2) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hexp : 2 * (M + 1) - 2 = 2 * M := by omega
  have hsub : (M + 1) - 1 = M := by omega
  rw [hexp, hsub]
  have hlhs : (∑ n ∈ Finset.range (M + 1), (Nat.choose M n : ℝ) ^ 2)
      = (Nat.choose (2 * M) M : ℝ) := by
    have := Nat.sum_range_choose_sq M
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
  have _hpos : ((M : ℝ) + 1) ≠ 0 := by positivity
  have h4 : ((4 : ℝ) ^ M) ≠ 0 := by positivity
  have hS := Kammler24.sum_cos_pow M
  rw [hlhs]
  push_cast
  rw [eq_div_of_mul_eq h4 hS]
  field_simp
