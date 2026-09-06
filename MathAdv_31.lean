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



/-- For `-1 < x < 1`, the derivative of `f x = 2 sin x + 5 arccos x` is
`2 cos x - 5 / √(1 - x ^ 2)`. -/
theorem dawkins_3_7_1_on_Ioo {x : ℝ} (h₁ : -1 < x) (h₂ : x < 1) :
    deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) x
      = 2 * Real.cos x - 5 / Real.sqrt (1 - x ^ 2) := by
  have hs : HasDerivAt (fun x : ℝ => 2 * Real.sin x) (2 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 2
  have ha : HasDerivAt (fun x : ℝ => 5 * Real.arccos x)
      (5 * -(1 / Real.sqrt (1 - x ^ 2))) x :=
    (Real.hasDerivAt_arccos (by linarith) (by linarith)).const_mul 5
  have hsum : HasDerivAt (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x)
      (2 * Real.cos x + 5 * -(1 / Real.sqrt (1 - x ^ 2))) x := hs.add ha
  rw [hsum.deriv]; ring

/-- The unrestricted, global form of the statement is false: the two functions differ at `x = 1`,
where `Real.arccos` fails to be differentiable. -/
theorem dawkins_3_7_1_not_eq_everywhere :
    deriv (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) ≠
      (fun x : ℝ => 2 * Real.cos x - 5 / Real.sqrt (1 - x ^ 2)) := by
  intro h
  have h1 := congrFun h 1
  have hnd : ¬ DifferentiableAt ℝ (fun x : ℝ => 2 * Real.sin x + 5 * Real.arccos x) 1 := by
    intro hd
    have h5 : DifferentiableAt ℝ (fun x : ℝ => 5 * Real.arccos x) 1 := by
      have := hd.sub (Real.differentiable_sin.differentiableAt.const_mul 2)
      simpa using this
    have h5' : DifferentiableAt ℝ (fun x : ℝ => (5 : ℝ)⁻¹ * (5 * Real.arccos x)) 1 :=
      h5.const_mul _
    have harc : DifferentiableAt ℝ Real.arccos 1 := by
      have e : (fun x : ℝ => (5 : ℝ)⁻¹ * (5 * Real.arccos x)) = Real.arccos := by
        funext y; ring
      rwa [e] at h5'
    exact absurd (Real.differentiableAt_arccos.mp harc).2 (by simp)
  rw [deriv_zero_of_not_differentiableAt hnd] at h1
  simp at h1
  have := Real.cos_one_pos
  linarith
