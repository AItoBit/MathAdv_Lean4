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

/-
The original statement, as an equality of functions on all of `ℝ`:

theorem dawkins_3_7_1 :
  deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) =
    (fun x : ℝ => 2 * Real.cos x - 5 / Real.sqrt (1 - x^2)) := by
  sorry

This global version is FALSE: `Real.arccos` is not differentiable at `x = 1`
(nor at `x = -1`), so the left-hand side is `0` there (Lean's `deriv` returns `0`
at points of non-differentiability), while the right-hand side evaluates to
`2 * Real.cos 1 - 5 / Real.sqrt 0 = 2 * Real.cos 1 ≠ 0`.
This is proved below in `dawkins_3_7_1_global_false`.

The intended (and correct) statement is the pointwise one on the domain
`-1 < x < 1` of the derivative formula, proved as `dawkins_3_7_1` below.
-/

/-- **Derivative of `f x = 2 sin x + 5 arccos x`.**
For `x` in the open interval `(-1, 1)` (where `arccos` is differentiable),
`f' x = 2 cos x - 5 / √(1 - x²)`. -/
theorem dawkins_3_7_1 {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) x =
      2 * Real.cos x - 5 / Real.sqrt (1 - x ^ 2) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hne1 : x ≠ -1 := by intro h; rw [h] at hx1; linarith
  have hne2 : x ≠ 1 := by intro h; rw [h] at hx2; linarith
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.sin x) (2 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 2
  have h2 : HasDerivAt (fun x : ℝ => 5 * Real.arccos x)
      (5 * -(1 / Real.sqrt (1 - x ^ 2))) x :=
    (Real.hasDerivAt_arccos hne1 hne2).const_mul 5
  have h3 : HasDerivAt (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x)
      (2 * Real.cos x + 5 * -(1 / Real.sqrt (1 - x ^ 2))) x := h1.add h2
  rw [h3.deriv]
  ring

/-- The original, unrestricted statement is false: the two functions differ at `x = 1`. -/
theorem dawkins_3_7_1_global_false :
    deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) ≠
      (fun x : ℝ => 2 * Real.cos x - 5 / Real.sqrt (1 - x ^ 2)) := by
  intro h
  have hnd : ¬ DifferentiableAt ℝ (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) 1 := by
    intro hd
    have harc : DifferentiableAt ℝ Real.arccos 1 := by
      have hsin : DifferentiableAt ℝ (fun x : ℝ => 2 * Real.sin x) 1 :=
        (Real.differentiable_sin 1).const_mul 2
      have h5 : DifferentiableAt ℝ (fun x : ℝ => 5 * Real.arccos x) 1 := by
        simpa using hd.sub hsin
      simpa using h5.const_mul (5 : ℝ)⁻¹
    exact absurd (Real.differentiableAt_arccos.mp harc).2 (by norm_num)
  have hL : deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) 1 = 0 :=
    deriv_zero_of_not_differentiableAt hnd
  have := congrFun h 1
  rw [hL] at this
  norm_num at this
  have hcos : 0 < Real.cos 1 := Real.cos_one_pos
  linarith
