import Mathlib

/-!
# The ideal `(x - (1 - √3))` is maximal in `ℂ[x]` and contains `x³ - 3x² + 2`

Here `z : ℂ` is any square root of `3` (so `1 - z` plays the role of `1 - √3`).
-/

open Polynomial

/-- `1 - z` is a root of `x³ - 3x² + 2` whenever `z² = 3`. -/
lemma isRoot_cubic_of_sq_eq_three (z : ℂ) (hz : z ^ 2 = (3 : ℂ)) :
    (X ^ 3 - C (3 : ℂ) * X ^ 2 + C (2 : ℂ)).IsRoot (1 - z) := by
  simp only [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination (-z) * hz

theorem Q23
    (z : ℂ) (hz : z ^ 2 = (3 : ℂ)) :
  let I : Ideal (Polynomial ℂ) :=
        Ideal.span ({Polynomial.X - Polynomial.C ((1 : ℂ) - z)} :
          Set (Polynomial ℂ))
  let f : Polynomial ℂ :=
        Polynomial.X ^ 3
        - Polynomial.C (3 : ℂ) * Polynomial.X ^ 2
        + Polynomial.C (2 : ℂ)
  (I.IsMaximal) ∧ (f ∈ I) := by
  intro I f
  constructor
  · exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)
  · rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
    exact isRoot_cubic_of_sq_eq_three z hz
