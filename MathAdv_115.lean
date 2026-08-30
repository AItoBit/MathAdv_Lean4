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

/-- The Wallis-type evaluation of `∫_0^π cos^(2m)`. -/
lemma integral_cos_even_pow_zero_pi (m : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ (2 * m))
      = Real.pi * ∏ i ∈ Finset.range m, ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [h, integral_cos_pow (2 * m), ih]
      simp [Finset.prod_range_succ, Real.sin_pi]
      have h2 : (2 : ℝ) * (m : ℝ) + 2 ≠ 0 := by positivity
      field_simp

/-- Rescaling `s ↦ π s` turns `∫_0^1 cos(π s)^k` into `π⁻¹ ∫_0^π cos^k`. -/
lemma integral_cos_pi_mul_pow (k : ℕ) :
    (∫ s in (0 : ℝ)..1, Real.cos (Real.pi * s) ^ k)
      = Real.pi⁻¹ * ∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ k := by
  have h := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := (1 : ℝ)) (c := Real.pi) (f := fun x : ℝ => Real.cos x ^ k)
    (Real.pi_ne_zero)
  simpa [smul_eq_mul] using h

/-- The Wallis product for the central binomial coefficient. -/
lemma four_pow_mul_wallis_prod (m : ℕ) :
    (4 : ℝ) ^ m * ∏ i ∈ Finset.range m, ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2))
      = (Nat.choose (2 * m) m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
          = (Nat.choose (2 * m) m : ℝ) * (2 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1)) := by
        have hfac : (Nat.choose (2 * (m + 1)) (m + 1)) * (m + 1) * (m + 1)
            = (Nat.choose (2 * m) m) * (2 * (2 * m + 1)) * (m + 1) := by
          have h1 : Nat.choose (2 * m) m * (m.factorial * m.factorial) = (2 * m).factorial := by
            have := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_eq (by ring :
              m = m) |>.trans (Nat.le_mul_of_pos_left m (by norm_num) : m ≤ 2 * m))
            simpa [Nat.two_mul, Nat.add_sub_cancel, mul_assoc] using this
          have h2 : Nat.choose (2 * (m + 1)) (m + 1) * ((m + 1).factorial * (m + 1).factorial)
              = (2 * (m + 1)).factorial := by
            have := Nat.choose_mul_factorial_mul_factorial
              (Nat.le_mul_of_pos_left (m + 1) (by norm_num) : m + 1 ≤ 2 * (m + 1))
            simpa [Nat.two_mul, Nat.add_sub_cancel, mul_assoc] using this
          have h3 : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
            have : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
            rw [this, Nat.factorial_succ, Nat.factorial_succ]
            ring
          have hpos : 0 < (m.factorial * m.factorial) := by positivity
          have key : Nat.choose (2 * (m + 1)) (m + 1) * (m + 1) * (m + 1)
              * (m.factorial * m.factorial)
              = Nat.choose (2 * m) m * (2 * (2 * m + 1)) * (m + 1) * (m.factorial * m.factorial) := by
            have e1 : Nat.choose (2 * (m + 1)) (m + 1) * (m + 1) * (m + 1)
                * (m.factorial * m.factorial)
                = Nat.choose (2 * (m + 1)) (m + 1) * ((m + 1).factorial * (m + 1).factorial) := by
              simp [Nat.factorial_succ]; ring
            rw [e1, h2, h3, ← h1]
            ring
          exact Nat.eq_of_mul_eq_mul_right hpos key
        have hcast : ((Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 1)
            = ((Nat.choose (2 * m) m : ℕ) : ℝ) * (2 * (2 * (m : ℝ) + 1)) * ((m : ℝ) + 1) := by
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hfac
        have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp at hcast ⊢
        linarith [hcast]
      rw [Finset.prod_range_succ, hstep, ← ih]
      have hm2 : (2 : ℝ) * (m : ℝ) + 2 ≠ 0 := by positivity
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

theorem kammler_24_b
    (N : ℕ) (hN : 2 ≤ N) :
  (∑ n ∈ Finset.range N, (Nat.choose (N - 1) n : ℝ) ^ 2)
    = (4 : ℝ) ^ (N - 1)
        * ∫ s in (0 : ℝ)..1, (Real.cos (Real.pi * s)) ^ (2 * N - 2)
  ∧
  (∑ n ∈ Finset.range N, (Nat.choose (N - 1) n : ℝ) ^ 2)
    = (Nat.choose (2 * N - 2) (N - 1) : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : (m + 1) - 1 = m := by omega
  have hm2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have hsum : (∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) ^ 2)
      = (Nat.choose (2 * m) m : ℝ) := by
    have := Nat.sum_range_choose_sq m
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
  rw [hm, hm2]
  refine ⟨?_, hsum⟩
  rw [hsum, integral_cos_pi_mul_pow, integral_cos_even_pow_zero_pi]
  rw [← four_pow_mul_wallis_prod m]
  field_simp
