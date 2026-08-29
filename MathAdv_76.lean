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
# Minimum modulus principle (complex analysis, problem 4.9)

**Problem.** Suppose `f` is analytic and *non*constant on a region `D` and suppose `f z ≠ 0`
for all `z ∈ D`.  Explain why `|f z|` does not have a minimum in `D`.

**Answer to the multiple-choice question: (b) the maximum modulus principle** — applied to `1/f`
(which is analytic on `D` because `f` never vanishes) it yields the minimum modulus principle
used below.

The statement as originally transcribed assumes `f` is *constant* on `D`; with that hypothesis
the claim is false, since a constant function attains its (constant) modulus everywhere on the
nonempty region `D`.  It is preserved, commented out, below, together with a proof of its
negation `question_2_constant_counterexample`, and a corrected version `question_2` where the
hypothesis is nonconstancy.
-/

/-
-- FALSE as stated: with `f` constant, `‖f‖` *does* attain a minimum on the nonempty set `D`.
theorem question_2
    (D : Set ℂ) (f : ℂ → ℂ)
    (hDopen : IsOpen D)
    (hDconn : IsConnected D)
    (h_analytic : AnalyticOn ℂ f D)
    (h_nonzero : ∀ z ∈ D, f z ≠ 0)
    (h_const : ∀ ⦃z w⦄, z ∈ D → w ∈ D → f z = f w) :
    ¬ ∃ z0 ∈ D, ∀ z ∈ D, ‖f z0‖ ≤ ‖f z‖ := by
  sorry
-/

/-- Refutation of the statement above: if `f` is constant on the (nonempty) region `D`, then
`‖f‖` *does* attain a minimum on `D`.  Note that neither analyticity nor nonvanishing is
needed for this. -/
theorem question_2_constant_counterexample
    (D : Set ℂ) (f : ℂ → ℂ)
    (hDconn : IsConnected D)
    (h_const : ∀ ⦃z w⦄, z ∈ D → w ∈ D → f z = f w) :
    ∃ z0 ∈ D, ∀ z ∈ D, ‖f z0‖ ≤ ‖f z‖ := by
  obtain ⟨z0, hz0⟩ := hDconn.nonempty
  exact ⟨z0, hz0, fun z hz => le_of_eq (congrArg norm (h_const hz0 hz))⟩

/-- **Minimum modulus principle.** If `f` is analytic and nonconstant on a region `D` and
`f` does not vanish on `D`, then `‖f‖` has no minimum on `D`. -/
theorem question_2
    (D : Set ℂ) (f : ℂ → ℂ)
    (hDopen : IsOpen D)
    (hDconn : IsConnected D)
    (h_analytic : AnalyticOn ℂ f D)
    (h_nonzero : ∀ z ∈ D, f z ≠ 0)
    (h_nonconst : ∃ z ∈ D, ∃ w ∈ D, f z ≠ f w) :
    ¬ ∃ z0 ∈ D, ∀ z ∈ D, ‖f z0‖ ≤ ‖f z‖ := by
  rintro ⟨z0, hz0, hmin⟩
  have hnhd : AnalyticOnNhd ℂ f D := hDopen.analyticOn_iff_analyticOnNhd.mp h_analytic
  have hDmem : D ∈ nhds z0 := hDopen.mem_nhds hz0
  have hdiff : ∀ᶠ z in nhds z0, DifferentiableAt ℂ f z := by
    filter_upwards [hDmem] with z hz using (hnhd z hz).differentiableAt
  have hlocmin : IsLocalMin (norm ∘ f) z0 := by
    filter_upwards [hDmem] with z hz using hmin z hz
  rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm hdiff hlocmin with heq | h0
  · have hconst : Set.EqOn f (fun _ => f z0) D :=
      hnhd.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hDconn.isPreconnected hz0 heq
    obtain ⟨z, hz, w, hw, hne⟩ := h_nonconst
    exact hne ((hconst hz).trans (hconst hw).symm)
  · exact h_nonzero z0 hz0 h0
