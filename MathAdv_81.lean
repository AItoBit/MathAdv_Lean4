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
## Integral of `z ^ n` over a closed curve in `ℂ \ {0}` (`n ≠ -1`)

The original statement below is not provable as literally written: with no
regularity assumption on `Γ`, the pointwise conditions `Γ 0 = Γ 1` and `Γ t ≠ 0`
say nothing about `deriv Γ`. Indeed `Γ t = exp t` for `t ≠ 1` and `Γ 1 = 1` is
closed and nowhere vanishing, yet
`∫ t in (0:ℝ)..1, (Γ t) ^ (0 : ℤ) * deriv Γ t = e - 1 ≠ 0`; this is proved below
in `question_7_without_regularity_false`.

The corrected statement below adds the standard hypotheses that `Γ` is
differentiable with continuous derivative (a `C¹` cycle).
-/

/-- **Integral of `z ^ n` along a cycle avoiding the origin.**
If `n ≠ -1` and `Γ : ℝ → ℂ` is a continuously differentiable closed curve
(`Γ 0 = Γ 1`) avoiding `0`, then `∫_Γ z ^ n dz = 0`, since `z ^ (n+1) / (n+1)` is
a primitive of `z ^ n` on `ℂ \ {0}`. -/
theorem question_7
    (n : ℤ) (hn : n ≠ (-1 : ℤ))
    (Γ : ℝ → ℂ)
    (hΓ_diff : ∀ t : ℝ, DifferentiableAt ℝ Γ t)
    (hΓ_deriv_cont : Continuous (deriv Γ))
    (hΓ_closed : Γ 0 = Γ 1)
    (hΓ_away : ∀ t : ℝ, Γ t ≠ 0) :
    (∫ t in (0 : ℝ)..1, (Γ t) ^ (n : ℤ) * deriv Γ t) = 0 := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    apply hn
    have : ((n : ℂ)) = ((-1 : ℤ) : ℂ) := by push_cast; linear_combination h
    exact_mod_cast this
  have hΓcont : Continuous Γ := by
    have : ∀ t : ℝ, ContinuousAt Γ t := fun t => (hΓ_diff t).continuousAt
    exact continuous_iff_continuousAt.mpr this
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => Γ s ^ (n + 1) / ((n : ℂ) + 1))
        ((Γ t) ^ (n : ℤ) * deriv Γ t) t := by
    intro t _
    have h1 : HasDerivAt (fun z : ℂ => z ^ (n + 1))
        (((n : ℂ) + 1) * Γ t ^ (n + 1 - 1)) (Γ t) := by
      have := hasDerivAt_zpow (n + 1) (Γ t) (Or.inl (hΓ_away t))
      simpa using this
    have h2 := HasDerivAt.comp t h1 (hΓ_diff t).hasDerivAt
    have h3 := h2.div_const ((n : ℂ) + 1)
    have h_eval : (((n : ℂ) + 1) * Γ t ^ (n + 1 - 1) * deriv Γ t) / ((n : ℂ) + 1)
        = Γ t ^ (n : ℤ) * deriv Γ t := by
      have hsub : n + 1 - 1 = n := by ring
      rw [hsub]
      have hdiv : (((n : ℂ) + 1) * (Γ t ^ (n : ℤ) * deriv Γ t)) / ((n : ℂ) + 1)
          = Γ t ^ (n : ℤ) * deriv Γ t :=
        mul_div_cancel_left₀ (Γ t ^ (n : ℤ) * deriv Γ t) hn1
      rwa [← mul_assoc] at hdiv
    rwa [h_eval] at h3
  have hint : IntervalIntegrable (fun t => (Γ t) ^ (n : ℤ) * deriv Γ t)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hΓcont.zpow₀ n (fun x => Or.inl (hΓ_away x))).mul hΓ_deriv_cont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, hΓ_closed]
  ring

/-- **The original statement is false without a regularity hypothesis on `Γ`.**
Taking `n = 0` and the (discontinuous at `1`) closed, nowhere-vanishing curve
`Γ t = exp t` for `t ≠ 1`, `Γ 1 = 1`, one gets
`∫ t in (0:ℝ)..1, (Γ t) ^ (0 : ℤ) * deriv Γ t = e - 1 ≠ 0`. -/
theorem question_7_without_regularity_false :
    ¬ (∀ (n : ℤ), n ≠ (-1 : ℤ) → ∀ Γ : ℝ → ℂ, Γ 0 = Γ 1 → (∀ t : ℝ, Γ t ≠ 0) →
        (∫ t in (0 : ℝ)..1, (Γ t) ^ (n : ℤ) * deriv Γ t) = 0) := by
  intro H
  set Γ : ℝ → ℂ := fun t => if t = 1 then 1 else Complex.exp (t : ℂ) with hΓdef
  have hexp_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ))
      (Complex.exp (t : ℂ)) t := fun t => (Complex.hasDerivAt_exp (t : ℂ)).comp_ofReal
  have hderiv : ∀ t : ℝ, t ≠ 1 → deriv Γ t = Complex.exp (t : ℂ) := by
    intro t ht
    have hev : Γ =ᶠ[nhds t] fun s : ℝ => Complex.exp (s : ℂ) := by
      filter_upwards [(isOpen_compl_singleton (x := (1 : ℝ))).mem_nhds ht] with s hs
      have hs1 : s ≠ 1 := hs
      simp [hΓdef, hs1]
    rw [hev.deriv_eq, (hexp_deriv t).deriv]
  have hclosed : Γ 0 = Γ 1 := by norm_num [hΓdef]
  have hne : ∀ t : ℝ, Γ t ≠ 0 := by
    intro t
    by_cases ht : t = 1 <;> simp [hΓdef, ht, Complex.exp_ne_zero]
  have hzero := H 0 (by decide) Γ hclosed hne
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 →
      (Γ x) ^ (0 : ℤ) * deriv Γ x = Complex.exp (x : ℂ) := by
    have hne1 : ∀ᵐ x : ℝ, x ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne1] with x hx _
    rw [hderiv x hx]
    simp
  rw [intervalIntegral.integral_congr_ae hae] at hzero
  have hint : (∫ t in (0 : ℝ)..1, Complex.exp (t : ℂ))
      = Complex.exp ((1 : ℝ) : ℂ) - Complex.exp ((0 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hexp_deriv t)
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hint] at hzero
  have : Complex.exp ((1 : ℝ) : ℂ) = 1 := by
    have := hzero
    simp at this
    linear_combination this
  rw [← Complex.ofReal_exp] at this
  have : Real.exp 1 = 1 := by exact_mod_cast this
  simp [Real.exp_eq_one_iff] at this

#print axioms question_7
#print axioms question_7_without_regularity_false
