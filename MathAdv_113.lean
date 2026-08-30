import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open MeasureTheory

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-- The Heaviside step function. -/
noncomputable def heaviside_kammler23 (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else 0

/-- `u(x) = e^{-α x} h(x)`, viewed as a complex-valued function of a real variable. -/
noncomputable def kammlerU_kammler23 (α : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (-α * x) : ℂ) * ((heaviside_kammler23 x : ℝ) : ℂ)

/-- Convolution of two complex-valued functions on `ℝ`. -/
noncomputable def kammlerConv_kammler23 (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, f t * g (x - t)

/-- The iterated convolution powers `u_n` of `u` (with the junk value `u_0 := 0`). -/
noncomputable def kammlerUPow_kammler23 (α : ℝ) : ℕ → ℝ → ℂ
  | 0       => fun _ => 0
  | 1       => kammlerU_kammler23 α
  | n + 2   =>
      kammlerConv_kammler23
        (kammlerUPow_kammler23 α (n + 1))
        (kammlerU_kammler23 α)

/-- The integrand of the convolution defining `u_{n+2}` is the indicator function of `[0, x]`
applied to `t ↦ e^{-α x} t^n / n!`. -/
lemma kammler23_integrand (α : ℝ) (n : ℕ) (x t : ℝ) :
    ((t : ℂ) ^ n * (Real.exp (-α * t) : ℂ) * ((heaviside_kammler23 t : ℝ) : ℂ)
        / (Nat.factorial n : ℂ))
      * ((Real.exp (-α * (x - t)) : ℂ) * ((heaviside_kammler23 (x - t) : ℝ) : ℂ))
      = Set.indicator (Set.Icc (0 : ℝ) x)
          (fun t : ℝ => ((Real.exp (-α * x) : ℂ) / (Nat.factorial n : ℂ)) * (t : ℂ) ^ n) t := by
  have hexp : (Real.exp (-α * t) : ℂ) * (Real.exp (-α * (x - t)) : ℂ)
      = (Real.exp (-α * x) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
  rw [Set.indicator_apply]
  by_cases ht : 0 ≤ t
  · by_cases hxt : t ≤ x
    · have hmem : t ∈ Set.Icc (0 : ℝ) x := ⟨ht, hxt⟩
      have hxt' : (0 : ℝ) ≤ x - t := by linarith
      simp only [heaviside_kammler23, if_pos ht, if_pos hxt', if_pos hmem,
        Complex.ofReal_one, mul_one]
      linear_combination ((t : ℂ) ^ n / (Nat.factorial n : ℂ)) * hexp
    · have hxt' : ¬ (0 : ℝ) ≤ x - t := by intro h; exact hxt (by linarith)
      simp [heaviside_kammler23, ht, hxt, hxt', Set.mem_Icc]
  · simp [heaviside_kammler23, ht, Set.mem_Icc]

/-- The integral of `t ↦ t^n` over `[0, x]` for `x ≥ 0`, as a complex-valued integral. -/
lemma kammler23_pow_integral (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in Set.Icc (0 : ℝ) x, (t : ℂ) ^ n) = (x : ℂ) ^ (n + 1) / ((n : ℂ) + 1) := by
  have h1 : (∫ t in Set.Icc (0 : ℝ) x, (t : ℂ) ^ n)
      = ((∫ t in Set.Icc (0 : ℝ) x, t ^ n : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx, integral_pow]
  push_cast
  simp

/-- **Kammler, Exercise 4.9.**  With `u(x) = e^{-α x} h(x)` (`h` the Heaviside step), the
`(n+1)`-fold convolution power of `u` is `u_{n+1}(x) = x^n e^{-α x} h(x) / n!`.
(The hypothesis `0 < α` is part of the original statement; the identity in fact holds for
every real `α`.) -/
theorem kammler_23
    (α : ℝ) (hα : 0 < α) :
    ∀ (n : ℕ) (x : ℝ),
      kammlerUPow_kammler23 α (n + 1) x =
        (((x : ℂ) ^ n
            * (Real.exp (-α * x) : ℂ)
            * ((heaviside_kammler23 x : ℝ) : ℂ))
          / (Nat.factorial n : ℂ)) := by
  intro n
  induction n with
  | zero => intro x; simp [kammlerUPow_kammler23, kammlerU_kammler23]
  | succ n ih =>
    intro x
    have hstep : kammlerUPow_kammler23 α (n + 2) x
        = ∫ t : ℝ, kammlerUPow_kammler23 α (n + 1) t * kammlerU_kammler23 α (x - t) := rfl
    rw [hstep]
    have hint : ∀ t : ℝ, kammlerUPow_kammler23 α (n + 1) t * kammlerU_kammler23 α (x - t)
        = Set.indicator (Set.Icc (0 : ℝ) x)
          (fun t : ℝ => ((Real.exp (-α * x) : ℂ) / (Nat.factorial n : ℂ)) * (t : ℂ) ^ n) t := by
      intro t
      rw [ih t, kammlerU_kammler23]
      exact kammler23_integrand α n x t
    rw [funext hint, integral_indicator measurableSet_Icc, integral_const_mul]
    by_cases hx : 0 ≤ x
    · rw [kammler23_pow_integral n hx]
      have hfac : ((Nat.factorial (n + 1) : ℕ) : ℂ) = ((n : ℂ) + 1) * (Nat.factorial n : ℂ) := by
        push_cast [Nat.factorial_succ]; ring
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      simp only [heaviside_kammler23, if_pos hx, Complex.ofReal_one, mul_one, hfac]
      field_simp
    · have hempty : Set.Icc (0 : ℝ) x = ∅ :=
        Set.Icc_eq_empty (by intro h; exact hx h)
      rw [hempty]
      simp [heaviside_kammler23, hx]
