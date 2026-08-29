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
# Weierstrass approximation theorem

Let `f` be continuous on the closed bounded interval `[a,b] ⊆ ℝ`. Then for every `ε > 0`
there is a polynomial `P` with `|f x - P x| < ε` for all `x ∈ [a,b]`.

The classical Fourier-analytic route to this statement (approximating `e^{ix}` uniformly by
polynomials, namely by partial sums of its power series) goes through **Fejér's theorem**:
Cesàro means of the Fourier series of a continuous periodic function converge to it uniformly,
so trigonometric polynomials approximate `f` uniformly, and each `e^{inx}` is in turn
approximated uniformly by polynomials on a bounded interval.
So the answer to the multiple-choice question is **(a) Fejér's theorem**.
-/

/-- **Weierstrass approximation theorem**: a function continuous on `Set.Icc a b` is uniformly
approximated on `Set.Icc a b` by polynomials. -/
theorem stein_10 {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∀ ε : ℝ, 0 < ε → ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc a b, |f x - P.eval x| < ε := by
  intro ε hε
  set F : C(Set.Icc a b, ℝ) := ⟨Set.restrict _ f, hf.restrict⟩ with hF
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b F ε hε
  refine ⟨p, fun x hx => ?_⟩
  have h := ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn (Set.Icc a b) - F) ⟨x, hx⟩
  simp [hF, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at h
  calc |f x - p.eval x| = |p.eval x - f x| := abs_sub_comm _ _
    _ ≤ _ := h
    _ < ε := hp
