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

namespace Nonarchimedean

/-- If an absolute value satisfies the ultrametric inequality, then it is bounded by `1`
on the image of the natural numbers. -/
theorem natCast_le_one_of_ultrametric {k : Type} [Field k] (abs : k → ℝ)
    (h_abs : IsAbsoluteValue abs)
    (hult : ∀ x y : k, abs (x + y) ≤ max (abs x) (abs y)) (n : ℕ) :
    abs ((n : k)) ≤ 1 := by
  letI : IsAbsoluteValue abs := h_abs
  induction n with
  | zero => simp [IsAbsoluteValue.abv_zero abs]
  | succ m ih =>
      have : ((m + 1 : ℕ) : k) = (m : k) + 1 := by push_cast; ring
      rw [this]
      refine (hult (m : k) 1).trans ?_
      simp [IsAbsoluteValue.abv_one abs, ih]

/-- Binomial bound: if `abs` is bounded by `1` on natural numbers, then
`abs (x + y) ^ N ≤ (N + 1) * max (abs x) (abs y) ^ N`. -/
theorem pow_add_le_of_natCast_le_one {k : Type} [Field k] (abs : k → ℝ)
    (h_abs : IsAbsoluteValue abs)
    (hnat : ∀ n : ℕ, 0 < n → abs ((n : k)) ≤ 1) (x y : k) (N : ℕ) :
    abs (x + y) ^ N ≤ (N + 1) * max (abs x) (abs y) ^ N := by
  letI : IsAbsoluteValue abs := h_abs
  set M := max (abs x) (abs y) with hM
  have hMx : abs x ≤ M := le_max_left _ _
  have hMy : abs y ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (IsAbsoluteValue.abv_nonneg abs x) hMx
  have hpow : abs (x + y) ^ N = abs ((x + y) ^ N) :=
    (IsAbsoluteValue.abv_pow abs (x + y) N).symm
  rw [hpow, add_pow]
  refine (IsAbsoluteValue.abv_sum abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (N + 1),
      abs (x ^ i * y ^ (N - i) * ((N.choose i : ℕ) : k)) ≤ M ^ N := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hchoose : 0 < N.choose i := Nat.choose_pos hiN
    have h1 : abs (x ^ i * y ^ (N - i) * ((N.choose i : ℕ) : k))
        = abs x ^ i * abs y ^ (N - i) * abs ((N.choose i : ℕ) : k) := by
      rw [IsAbsoluteValue.abv_mul abs, IsAbsoluteValue.abv_mul abs,
        IsAbsoluteValue.abv_pow abs, IsAbsoluteValue.abv_pow abs]
    rw [h1]
    have hb1 : abs ((N.choose i : ℕ) : k) ≤ 1 := hnat _ hchoose
    have hb0 : 0 ≤ abs ((N.choose i : ℕ) : k) := IsAbsoluteValue.abv_nonneg abs _
    calc abs x ^ i * abs y ^ (N - i) * abs ((N.choose i : ℕ) : k)
        ≤ M ^ i * M ^ (N - i) * 1 := by
          gcongr
      _ = M ^ N := by
          rw [mul_one, ← pow_add, Nat.add_sub_cancel' hiN]
  calc ∑ i ∈ Finset.range (N + 1), abs (x ^ i * y ^ (N - i) * ((N.choose i : ℕ) : k))
      ≤ ∑ _i ∈ Finset.range (N + 1), M ^ N := Finset.sum_le_sum hterm
    _ = (N + 1) * M ^ N := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- If `a ^ N ≤ (N + 1) * M ^ N` for all `N`, with `M ≥ 0`, then `a ≤ M`. -/
theorem le_of_pow_le_linear_mul_pow {a M : ℝ} (hM : 0 ≤ M)
    (h : ∀ N : ℕ, a ^ N ≤ (N + 1) * M ^ N) : a ≤ M := by
  by_contra hlt
  push_neg at hlt
  have ha0 : 0 < a := lt_of_le_of_lt hM hlt
  set r := M / a with hr
  have hr0 : 0 ≤ r := div_nonneg hM ha0.le
  have hr1 : r < 1 := (div_lt_one ha0).2 hlt
  have key : ∀ N : ℕ, (1 : ℝ) ≤ ((N : ℝ) + 1) * r ^ N := by
    intro N
    have hMr : M = r * a := by rw [hr]; field_simp
    have := h N
    rw [hMr, mul_pow] at this
    have hpos : (0 : ℝ) < a ^ N := pow_pos ha0 N
    have h2 : a ^ N ≤ (((N : ℝ) + 1) * r ^ N) * a ^ N := by
      calc a ^ N ≤ ((N : ℝ) + 1) * (r ^ N * a ^ N) := this
        _ = (((N : ℝ) + 1) * r ^ N) * a ^ N := by ring
    exact le_of_mul_le_mul_right (by linarith) hpos
  have htend : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1) * r ^ N) Filter.atTop (nhds 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have := h1.add h2
    simpa [add_mul] using this
  have hev := htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N, hN⟩ := hev.exists
  exact absurd (key N) (not_le.2 hN)

end Nonarchimedean

/-- An absolute value on a field is nonarchimedean (satisfies the ultrametric inequality)
if and only if it is bounded by `1` on the positive integers. -/
theorem question_8
  (k : Type) [Field k]
  (abs : k → ℝ)
  (h_abs : IsAbsoluteValue abs) :
  (∀ x y : k, abs (x + y) ≤ max (abs x) (abs y))
    ↔
  (∀ n : ℕ, 0 < n → abs (Nat.cast n : k) ≤ 1) := by
  constructor
  · intro hult n _
    exact Nonarchimedean.natCast_le_one_of_ultrametric abs h_abs hult n
  · intro hnat x y
    letI : IsAbsoluteValue abs := h_abs
    refine Nonarchimedean.le_of_pow_le_linear_mul_pow
      (le_max_iff.2 (Or.inl (IsAbsoluteValue.abv_nonneg abs _))) ?_
    intro N
    exact Nonarchimedean.pow_add_le_of_natCast_le_one abs h_abs hnat x y N
