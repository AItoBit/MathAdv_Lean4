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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Stein19

open Complex

/-- Orthogonality of the characters on `[0,1]`: the integral over `[0,1]` of
`exp (2π i (n - m) x)` is `1` if `n = m` and `0` otherwise. -/
lemma integral_exp_diff (n m : ℕ) :
    (∫ x in (0:ℝ)..(1:ℝ),
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - (m : ℂ)) * (x : ℂ))) =
      if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h]
    have hc : (2 * (Real.pi:ℂ) * Complex.I * ((n : ℂ) - (m : ℂ))) ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h2 : ((n:ℂ) - (m:ℂ)) ≠ 0 := by
        simp only [ne_eq, sub_eq_zero]
        exact_mod_cast h
      simp [h1, h2, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have hone : Complex.exp (2 * (Real.pi:ℂ) * Complex.I * ((n : ℂ) - (m : ℂ)) * ((1:ℝ):ℂ)) = 1 := by
      have hrw : (2 * (Real.pi:ℂ) * Complex.I * ((n : ℂ) - (m : ℂ)) * ((1:ℝ):ℂ))
          = ((n : ℤ) - (m : ℤ) : ℤ) * (2 * (Real.pi:ℂ) * Complex.I) := by
        push_cast; ring
      rw [hrw, Complex.exp_int_mul_two_pi_mul_I]
    rw [hone]
    simp

/-- Discrete orthogonality: the sum of `exp (2π i (n - m) j / N)` over `j = 0, …, N-1`
is `N` if `n = m` and `0` otherwise, for `n, m < N`. -/
lemma sum_exp_diff (N : ℕ) (n m : Fin N) :
    (∑ j : Fin N,
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℕ) - (m : ℕ) : ℂ) *
        (((j : ℕ) : ℝ) / (N : ℝ) : ℝ))) = if n = m then (N : ℂ) else 0 := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) n.isLt
  have hN : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h]
    have hterm : ∀ j : Fin N,
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℕ) - (m : ℕ) : ℂ) *
          ((((j : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ))
          = (Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
              (((n:ℕ) : ℂ) - ((m:ℕ) : ℂ)) / (N:ℂ))) ^ ((j : ℕ)) := by
      intro j
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have hpow : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
        (((n:ℕ) : ℂ) - ((m:ℕ) : ℂ)) / (N:ℂ))) ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have hrw : (N:ℂ) * (2 * (Real.pi:ℂ) * Complex.I * (((n:ℕ) : ℂ) - ((m:ℕ) : ℂ)) / (N:ℂ))
          = ((n:ℕ) - (m:ℕ) : ℤ) * (2 * (Real.pi:ℂ) * Complex.I) := by
        field_simp; push_cast; ring
      rw [hrw, Complex.exp_int_mul_two_pi_mul_I]
    have hne : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
        (((n:ℕ) : ℂ) - ((m:ℕ) : ℂ)) / (N:ℂ))) ≠ 1 := by
      intro hone
      rw [Complex.exp_eq_one_iff] at hone
      obtain ⟨k, hk⟩ := hone
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h2 : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
      rw [div_eq_iff hN] at hk
      have hk2 : ((n:ℕ) : ℂ) - ((m:ℕ) : ℂ) = (k : ℂ) * (N : ℂ) := by
        apply mul_left_cancel₀ h2; linear_combination hk
      have hk3 : ((n:ℕ) : ℤ) - ((m:ℕ) : ℤ) = k * (N:ℤ) := by exact_mod_cast hk2
      have h1 : ((n:ℕ):ℤ) < N := by exact_mod_cast n.isLt
      have hb2 : ((m:ℕ):ℤ) < N := by exact_mod_cast m.isLt
      have h3 : ((n:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by
        have hnm : (n:ℕ) ≠ (m:ℕ) := fun hh => h (Fin.ext hh)
        exact_mod_cast hnm
      have h4 : (0:ℤ) ≤ ((n:ℕ):ℤ) := Int.natCast_nonneg _
      have h5 : (0:ℤ) ≤ ((m:ℕ):ℤ) := Int.natCast_nonneg _
      rcases lt_trichotomy k 0 with hkneg | hk0 | hkpos
      · nlinarith
      · simp [hk0] at hk3; omega
      · nlinarith
    rw [Fin.sum_univ_eq_sum_range (fun i => (Complex.exp (2 * (Real.pi:ℂ) * Complex.I *
        (((n:ℕ) : ℂ) - ((m:ℕ) : ℂ)) / (N:ℂ))) ^ i) N, geom_sum_eq hne, hpow]
    simp

/-- Expansion of `|P(x)|²` as a double sum. -/
lemma normSq_expand (N : ℕ) (a : Fin N → ℂ) (x : ℝ) :
    ((‖∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))‖^2 : ℝ) : ℂ) =
    ∑ n : Fin N, ∑ m : Fin N, a n * (starRingEnd ℂ) (a m) *
      Complex.exp (2 * Real.pi * Complex.I * (((n:ℕ):ℂ) - ((m:ℕ):ℂ)) * (x:ℂ)) := by
  have h1 : ((‖∑ i : Fin N, a i *
        Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))‖^2 : ℝ) : ℂ)
      = (∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))) *
        (starRingEnd ℂ)
          (∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [h1, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [map_mul, ← Complex.exp_conj]
  rw [show (starRingEnd ℂ) (2 * (Real.pi:ℂ) * Complex.I * ((m:ℕ):ℂ) * (x:ℂ))
      = -(2 * (Real.pi:ℂ) * Complex.I * ((m:ℕ):ℂ) * (x:ℂ)) by
    simp [Complex.ext_iff]]
  have h2 : Complex.exp (2 * (Real.pi:ℂ) * Complex.I * (((n:ℕ):ℂ) - ((m:ℕ):ℂ)) * (x:ℂ))
      = Complex.exp (2 * (Real.pi:ℂ) * Complex.I * ((n:ℕ):ℂ) * (x:ℂ)) *
        Complex.exp (-(2 * (Real.pi:ℂ) * Complex.I * ((m:ℕ):ℂ) * (x:ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h2]; ring

/-- Parseval identity for a trigonometric polynomial: the mean square of `P` on `[0,1]`
equals the sum of the squared moduli of its coefficients. -/
lemma integral_normSq_eq (N : ℕ) (a : Fin N → ℂ) :
    (∫ x in (0:ℝ)..(1:ℝ),
      ‖∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))‖^2)
      = ∑ n : Fin N, ‖a n‖^2 := by
  have key : ((∫ x in (0:ℝ)..(1:ℝ),
      ‖∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) * (x:ℂ))‖^2 : ℝ) : ℂ)
      = ((∑ n : Fin N, ‖a n‖^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_expand N a]
    rw [intervalIntegral.integral_finset_sum
      (fun n _ => by apply Continuous.intervalIntegrable; fun_prop)]
    have step : ∀ n : Fin N,
        (∫ x in (0:ℝ)..(1:ℝ), ∑ m : Fin N, a n * (starRingEnd ℂ) (a m) *
          Complex.exp (2 * Real.pi * Complex.I * (((n:ℕ):ℂ) - ((m:ℕ):ℂ)) * (x:ℂ)))
          = a n * (starRingEnd ℂ) (a n) := by
      intro n
      rw [intervalIntegral.integral_finset_sum
        (fun m _ => by apply Continuous.intervalIntegrable; fun_prop)]
      have : ∀ m : Fin N,
          (∫ x in (0:ℝ)..(1:ℝ), a n * (starRingEnd ℂ) (a m) *
            Complex.exp (2 * Real.pi * Complex.I * (((n:ℕ):ℂ) - ((m:ℕ):ℂ)) * (x:ℂ)))
            = if n = m then a n * (starRingEnd ℂ) (a m) else 0 := by
        intro m
        rw [intervalIntegral.integral_const_mul, integral_exp_diff (n:ℕ) (m:ℕ)]
        by_cases hnm : n = m
        · simp [hnm]
        · have hv : (n:ℕ) ≠ (m:ℕ) := fun hh => hnm (Fin.ext hh)
          simp [hnm, hv]
      rw [Finset.sum_congr rfl (fun m _ => this m)]
      simp
    rw [Finset.sum_congr rfl (fun n _ => step n)]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => Complex.mul_conj' (a n))
  exact_mod_cast key

/-- Discrete Parseval identity: the sum of `|P(j/N)|²` over `j = 0, …, N-1` equals
`N` times the sum of the squared moduli of the coefficients. -/
lemma sum_normSq_eq (N : ℕ) (a : Fin N → ℂ) :
    (∑ j : Fin N, ‖∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) *
      ((((j:ℕ):ℝ) / (N:ℝ) : ℝ) : ℂ))‖^2) = (N : ℝ) * ∑ n : Fin N, ‖a n‖^2 := by
  have key : ((∑ j : Fin N, ‖∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i:ℕ):ℂ) *
      ((((j:ℕ):ℝ) / (N:ℝ) : ℝ) : ℂ))‖^2 : ℝ) : ℂ)
      = (((N : ℝ) * ∑ n : Fin N, ‖a n‖^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [normSq_expand N a]
    rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_comm]
    have hm : ∀ m : Fin N,
        (∑ j : Fin N, a n * (starRingEnd ℂ) (a m) *
          Complex.exp (2 * Real.pi * Complex.I * (((n:ℕ):ℂ) - ((m:ℕ):ℂ)) *
            ((((j:ℕ):ℝ) / (N:ℝ) : ℝ) : ℂ)))
          = if n = m then (N : ℂ) * (a n * (starRingEnd ℂ) (a m)) else 0 := by
      intro m
      rw [← Finset.mul_sum, sum_exp_diff N n m]
      by_cases hnm : n = m
      · simp [hnm]; ring
      · simp [hnm]
    rw [Finset.sum_congr rfl (fun m _ => hm m)]
    rw [Finset.sum_ite_eq Finset.univ n (fun m => (N : ℂ) * (a n * (starRingEnd ℂ) (a m)))]
    rw [if_pos (Finset.mem_univ n), Complex.mul_conj' (a n)]
    push_cast
    ring
  exact_mod_cast key

end Stein19

theorem stein_19 (N : ℕ) (a : Fin N → ℂ) :
  let P : ℝ → ℂ :=
    fun x => ∑ i : Fin N, a i * Complex.exp (2 * Real.pi * Complex.I * ((i : ℕ) : ℂ) * (x : ℂ))
  ∫ x in (0 : ℝ)..(1 : ℝ), ‖P x‖ ^ 2 =
    (1 / N : ℝ) * ∑ j : Fin N, ‖P ((j : ℕ) / N : ℝ)‖ ^ 2 := by
  intro P
  simp only [P]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · rw [Stein19.integral_normSq_eq N a, Stein19.sum_normSq_eq N a]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp

