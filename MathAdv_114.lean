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

/-- `f[n] = C(N-1, n)`, extended by zero outside `0 ≤ n ≤ N-1`. -/
noncomputable def f_kammler24 (N : ℕ) (n : ℤ) : ℂ :=
  if 0 ≤ n ∧ Int.toNat n ≤ N - 1 then
    (Nat.choose (N - 1) (Int.toNat n) : ℂ)
  else
    0

/-- `g[n] = ∑_m f[n - mN]`, the `N`-periodization of `f`. -/
noncomputable def g_kammler24 (N : ℕ) (n : ℤ) : ℂ :=
  ∑' m : ℤ, f_kammler24 N (n - (m : ℤ) * (N : ℤ))

/-- The Fourier transform of `f`. -/
noncomputable def Fhat_kammler24 (N : ℕ) (s : ℝ) : ℂ :=
  (1 / (N : ℂ)) *
    ∑ n ∈ Finset.range N,
      f_kammler24 N (n : ℤ) *
        Complex.exp (-2 * Real.pi * Complex.I * (s / (N : ℝ)) * (n : ℝ))

/-- The Fourier transform of `g`. -/
noncomputable def Ghat_kammler24 (N : ℕ) (k : ℤ) : ℂ :=
  (1 / (N : ℂ)) *
    ∑ n ∈ Finset.range N,
      g_kammler24 N (n : ℤ) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ((k : ℝ) / (N : ℝ)) * (n : ℝ))

/-- `f` vanishes at negative arguments. -/
lemma f_kammler24_eq_zero_of_neg (N : ℕ) {n : ℤ} (hn : n < 0) :
    f_kammler24 N n = 0 := by
  unfold f_kammler24
  rw [if_neg]
  rintro ⟨h, -⟩
  omega

/-- `f` vanishes at arguments `≥ N` (for `N ≥ 1`). -/
lemma f_kammler24_eq_zero_of_ge (N : ℕ) (hN : 1 ≤ N) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    f_kammler24 N n = 0 := by
  unfold f_kammler24
  rw [if_neg]
  rintro ⟨h0, h1⟩
  have h2 : (N : ℤ) ≤ (Int.toNat n : ℤ) := by
    rwa [Int.toNat_of_nonneg h0]
  have h3 : N ≤ Int.toNat n := by exact_mod_cast h2
  omega

/-- On the fundamental domain `0 ≤ n < N`, the periodization `g` agrees with `f`. -/
lemma g_kammler24_eq_f (N : ℕ) {n : ℤ} (h0 : 0 ≤ n) (h1 : n < (N : ℤ)) :
    g_kammler24 N n = f_kammler24 N n := by
  have hN : 1 ≤ N := by omega
  unfold g_kammler24
  have h : ∀ m : ℤ, m ≠ 0 → f_kammler24 N (n - m * (N : ℤ)) = 0 := by
    intro m hm
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · -- m ≤ -1, so n - m*N ≥ n + N ≥ N
      refine f_kammler24_eq_zero_of_ge N (by omega) ?_
      have hm1 : m ≤ -1 := by omega
      have : m * (N : ℤ) ≤ (-1) * (N : ℤ) := by
        apply mul_le_mul_of_nonneg_right hm1
        positivity
      omega
    · -- m ≥ 1, so n - m*N ≤ n - N < 0
      refine f_kammler24_eq_zero_of_neg N ?_
      have hm1 : (1 : ℤ) ≤ m := by omega
      have : (1 : ℤ) * (N : ℤ) ≤ m * (N : ℤ) := by
        apply mul_le_mul_of_nonneg_right hm1
        positivity
      omega
  rw [tsum_eq_single 0 h]
  simp

/-- The generating function identity: `∑_{n<N} C(N-1,n) z^n = (1+z)^{N-1}`. -/
lemma sum_f_kammler24_pow (N : ℕ) (hN : 1 ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range N, f_kammler24 N (n : ℤ) * z ^ n = (1 + z) ^ (N - 1) := by
  have hrange : N = (N - 1) + 1 := by omega
  rw [add_comm (1 : ℂ) z, add_pow]
  rw [← hrange]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < N := Finset.mem_range.mp hn
  have hf : f_kammler24 N (n : ℤ) = (Nat.choose (N - 1) n : ℂ) := by
    unfold f_kammler24
    rw [if_pos]
    · simp
    · refine ⟨by positivity, ?_⟩
      simp only [Int.toNat_natCast]
      omega
  rw [hf]
  ring

/-- Rewriting the exponential kernel as a power. -/
lemma exp_kernel_pow (z : ℂ) (n : ℕ) :
    Complex.exp (-2 * Real.pi * Complex.I * z * ((n : ℝ) : ℂ))
      = (Complex.exp (-2 * Real.pi * Complex.I * z)) ^ n := by
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The two transforms agree at integer frequencies: `G[k] = F(k)`. -/
theorem Ghat_kammler24_eq_Fhat_kammler24 (N : ℕ) (k : ℤ) :
    Ghat_kammler24 N k = Fhat_kammler24 N (k : ℝ) := by
  unfold Ghat_kammler24 Fhat_kammler24
  refine congrArg _ (Finset.sum_congr rfl ?_)
  intro n hn
  have hn' : n < N := Finset.mem_range.mp hn
  rw [g_kammler24_eq_f N (by positivity) (by exact_mod_cast hn')]

/-- **Kammler, Exercise 2.4.** The Fourier transform of `f[n] = C(N-1,n)` is
`F(s) = N⁻¹ (1 + e^{-2πis/N})^{N-1}`, and the Fourier transform of its `N`-periodization
`g` is `G[k] = N⁻¹ (1 + e^{-2πik/N})^{N-1}`. -/
theorem kammler_24_a
    (N : ℕ) (hN : 2 ≤ N) :
    (∀ s : ℝ,
      Fhat_kammler24 N s =
        (1 / (N : ℂ)) *
          (1 + Complex.exp (-2 * Real.pi * Complex.I * (s / (N : ℝ)))) ^ (N - 1))
    ∧
    (∀ k : ℤ,
      Ghat_kammler24 N k =
        (1 / (N : ℂ)) *
          (1 + Complex.exp (-2 * Real.pi * Complex.I *
                ((k : ℝ) / (N : ℝ)))) ^ (N - 1)) := by
  have hN1 : 1 ≤ N := by omega
  have key : ∀ z : ℂ,
      ∑ n ∈ Finset.range N,
        f_kammler24 N (n : ℤ) *
          Complex.exp (-2 * Real.pi * Complex.I * z * ((n : ℝ) : ℂ))
        = (1 + Complex.exp (-2 * Real.pi * Complex.I * z)) ^ (N - 1) := by
    intro z
    rw [← sum_f_kammler24_pow N hN1 (Complex.exp (-2 * Real.pi * Complex.I * z))]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [exp_kernel_pow z n]
  constructor
  · intro s
    unfold Fhat_kammler24
    rw [key ((s : ℂ) / ((N : ℝ) : ℂ))]
  · intro k
    unfold Ghat_kammler24
    have hg : ∀ n ∈ Finset.range N,
        g_kammler24 N (n : ℤ) *
          Complex.exp (-2 * Real.pi * Complex.I * ((k : ℝ) / (N : ℝ)) * (n : ℝ))
        = f_kammler24 N (n : ℤ) *
          Complex.exp (-2 * Real.pi * Complex.I * ((k : ℝ) / (N : ℝ)) * (n : ℝ)) := by
      intro n hn
      have hn' : n < N := Finset.mem_range.mp hn
      rw [g_kammler24_eq_f N (by positivity) (by exact_mod_cast hn')]
    rw [Finset.sum_congr rfl hg, key (((k : ℝ) : ℂ) / ((N : ℝ) : ℂ))]
