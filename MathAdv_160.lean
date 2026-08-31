import Mathlib

/-!
# Tu, Problem 23.3 : pullback of a top form under a diffeomorphism

The informal statement is: if `F : N → M` is a diffeomorphism of connected oriented
`n`-manifolds, then `∫_N F^*ω = ± ∫_M ω` for every compactly supported `n`-form `ω`,
the sign being `+` when `F` is orientation preserving and `-` when it is orientation
reversing.

The proof does **not** need Stokes' theorem: one reduces (via a partition of unity and
charts) to the change of variables formula in `ℝⁿ`, which is the analytic content of the
statement.  The theorem below is exactly that reduction target: the multivariate change
of variables formula on `Fin n → ℝ`, stating that for an injective `C¹` map `F` on a
measurable set `s`,

`∫_{F '' s} g = ∫_s |det (DF x)| * g (F x)`.

Here the Jacobian determinant appears in absolute value; the sign of `det DF` is precisely
what produces the `±` in the manifold statement.
-/

open MeasureTheory

/-- **Change of variables** in `ℝⁿ`: for a `C¹` map `F` which is injective on a
measurable set `s`, and any function `g`, the integral of `g` over `F '' s` equals the
integral over `s` of `|det (DF x)| * g (F x)`.  This is the analytic ingredient to which
the statement "`∫_N F^*ω = ± ∫_M ω` for a diffeomorphism `F`" reduces (no Stokes'
theorem required). -/
theorem Tu_23_3_changeOfVariables
    (n : ℕ)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s)
    (hF : ContDiff ℝ 1 F)
    (h_inj : Set.InjOn F s)
    (g : (Fin n → ℝ) → ℝ) :
    (∫ x in F '' s, g x ∂(MeasureTheory.volume))
      =
    (∫ x in s, (abs ((fderiv ℝ F x).det)) * g (F x) ∂(MeasureTheory.volume)) := by
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F (fderiv ℝ F x) s x := fun x _ =>
    ((hF.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt
  simpa [smul_eq_mul] using
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (volume : Measure (Fin n → ℝ)) hs hderiv h_inj g
