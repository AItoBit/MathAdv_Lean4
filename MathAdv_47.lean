import Mathlib

/-!
# Averaging points on the hyperbola `xy = 1`

If `(x₁, y₁)` and `(x₂, y₂)` lie on the branch of the hyperbola `xy = 1` in the first
quadrant, then their midpoint `(x, y)` satisfies `x * y ≥ 1`; this is the statement that
the region `{xy ≥ 1, x > 0}` above the hyperbola is convex.

The original statement, without any sign assumption, is **false**: see
`strang_13_1_30_counterexample` below.  We therefore prove the corrected version
`strang_13_1_30`, which adds the hypothesis that `x₁` and `x₂` are positive
(then `y₁ = 1 / x₁` and `y₂ = 1 / x₂` are positive too).
-/

/-- The statement without sign hypotheses is false: take `(x₁, y₁) = (1, 1)` and
`(x₂, y₂) = (-1, -1)`; the midpoint is the origin, where `xy = 0 < 1`. -/
theorem strang_13_1_30_counterexample :
    ¬ ∀ x₁ y₁ x₂ y₂ : ℝ, x₁ * y₁ = 1 → x₂ * y₂ = 1 →
      ((x₁ + x₂) / 2) * ((y₁ + y₂) / 2) ≥ 1 := by
  intro h
  have := h 1 1 (-1) (-1) (by norm_num) (by norm_num)
  norm_num at this

/-- Corrected version of the original problem (the hypotheses `0 < x₁`, `0 < x₂` were
added, since the statement is false without them).  If `x₁ y₁ = 1` and `x₂ y₂ = 1` with
`x₁, x₂ > 0`, then the averages `x = (x₁ + x₂)/2` and `y = (y₁ + y₂)/2` satisfy `xy ≥ 1`. -/
theorem strang_13_1_30
    {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (h₁ : x₁ * y₁ = 1) (h₂ : x₂ * y₂ = 1) :
    ((x₁ + x₂) / 2) * ((y₁ + y₂) / 2) ≥ 1 := by
  have hy₁ : y₁ = 1 / x₁ := by field_simp; linarith [h₁]
  have hy₂ : y₂ = 1 / x₂ := by field_simp; linarith [h₂]
  subst hy₁ hy₂
  rw [ge_iff_le, div_mul_div_comm, le_div_iff₀ (by norm_num : (0:ℝ) < 2 * 2)]
  have key : (x₁ - x₂) ^ 2 ≥ 0 := sq_nonneg _
  have h1 : (x₁ + x₂) * (1 / x₁ + 1 / x₂) = 2 + (x₁ / x₂ + x₂ / x₁) := by
    field_simp; ring
  rw [h1]
  have h2 : x₁ / x₂ + x₂ / x₁ ≥ 2 := by
    rw [ge_iff_le, div_add_div _ _ (ne_of_gt hx₂) (ne_of_gt hx₁),
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x₁ - x₂)]
  linarith
