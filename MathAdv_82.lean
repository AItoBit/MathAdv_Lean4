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
# Complex analysis 4.9

*Problem.* Suppose `f` is analytic and **nonconstant** on a region `D` and `f z ≠ 0` for all
`z ∈ D`. Explain why `|f z|` does not attain a minimum in `D`.

*Answer to the multiple-choice question:* **(b) the maximum modulus principle** — one applies it
to the analytic function `1 / f`, whose modulus would attain a maximum at a minimum point of `|f|`.

The statement as originally given assumed instead that `f` **is** constant on `D`; with that
hypothesis the conclusion is false, since a constant function attains its modulus everywhere on the
(nonempty) region `D`. The original statement is therefore refuted by
`question_2_hypotheses_force_minimum` below. The corrected statement is `question_2`.
-/

/-- Refutation of the constant-function statement: under its hypotheses (in particular `f` constant on the
nonempty connected set `D`), the modulus `‖f ·‖` *does* attain a minimum on `D`. -/
theorem question_2_hypotheses_force_minimum
    (D : Set ℂ) (f : ℂ → ℂ)
    (hDconn : IsConnected D)
    (h_const : ∀ ⦃z w⦄, z ∈ D → w ∈ D → f z = f w) :
    ∃ z0 ∈ D, ∀ z ∈ D, ‖f z0‖ ≤ ‖f z‖ := by
  obtain ⟨z0, hz0⟩ := hDconn.nonempty
  exact ⟨z0, hz0, fun z hz => by rw [h_const hz0 hz]⟩

/-- The hypotheses of the constant-function statement are indeed satisfiable, so the refutation above is
not vacuous. -/
theorem question_2_original_hypotheses_satisfiable :
    ∃ (D : Set ℂ) (f : ℂ → ℂ), IsOpen D ∧ IsConnected D ∧ AnalyticOn ℂ f D ∧
      (∀ z ∈ D, f z ≠ 0) ∧ (∀ ⦃z w⦄, z ∈ D → w ∈ D → f z = f w) := by
  refine ⟨Set.univ, fun _ => 1, isOpen_univ, ?_, analyticOn_const, ?_, ?_⟩
  · exact ⟨⟨0, trivial⟩, isPreconnected_univ⟩
  · intro z _; exact one_ne_zero
  · intro z w _ _; rfl

/-- **Corrected statement.** If `f` is analytic and nonconstant on a region (nonempty, open,
connected set) `D` and does not vanish on `D`, then `‖f ·‖` attains no minimum on `D`.

Proof: if `‖f z₀‖ ≤ ‖f z‖` for all `z ∈ D`, then `g = f⁻¹` is analytic on `D` and `‖g‖` attains a
maximum at `z₀`, so the maximum modulus principle forces `g`, hence `f`, to be constant on `D`. -/
theorem question_2
    (D : Set ℂ) (f : ℂ → ℂ)
    (hDopen : IsOpen D)
    (hDconn : IsConnected D)
    (h_analytic : AnalyticOn ℂ f D)
    (h_nonzero : ∀ z ∈ D, f z ≠ 0)
    (h_nonconst : ∃ z ∈ D, ∃ w ∈ D, f z ≠ f w) :
    ¬ ∃ z0 ∈ D, ∀ z ∈ D, ‖f z0‖ ≤ ‖f z‖ := by
  rintro ⟨z0, hz0, hmin⟩
  obtain ⟨a, ha, b, hb, hab⟩ := h_nonconst
  have hdiff : DifferentiableOn ℂ f D := (Complex.analyticOn_iff_differentiableOn hDopen).mp h_analytic
  have hginv : DifferentiableOn ℂ (fun z => (f z)⁻¹) D := fun z hz =>
    (hdiff z hz).inv (h_nonzero z hz)
  have hmax : IsMaxOn (norm ∘ fun z => (f z)⁻¹) D z0 := by
    intro z hz
    simp only [Function.comp_apply, norm_inv]
    have h0 : 0 < ‖f z0‖ := norm_pos_iff.mpr (h_nonzero z0 hz0)
    have hz_pos : 0 < ‖f z‖ := norm_pos_iff.mpr (h_nonzero z hz)
    exact (inv_le_inv₀ hz_pos h0).mpr (hmin z hz)
  have key := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hDconn.isPreconnected hDopen
    hginv hz0 hmax
  have hfa : f a = f z0 := by
    have := key ha
    simpa [inv_inj] using this
  have hfb : f b = f z0 := by
    have := key hb
    simpa [inv_inj] using this
  exact hab (hfa.trans hfb.symm)

/-- Answer to the multiple-choice question: which theorem or method answers the problem. -/
inductive Question2Method
  | fundamentalTheoremOfAlgebra
  | maximumModulusPrinciple
  | identityTheorem
  | liouvilleTheorem
  deriving DecidableEq, Repr

/-- The method used is the maximum modulus principle, option (b). -/
def question_2_answer : Question2Method := Question2Method.maximumModulusPrinciple
