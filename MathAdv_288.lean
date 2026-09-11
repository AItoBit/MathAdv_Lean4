import Mathlib

/-!
# A strict contraction that is not a uniform contraction

If `f : ℝ → ℝ` satisfies `|f u - f v| < |u - v|` for all `u ≠ v`, it need not follow that
there is a constant `c < 1` with `|f u - f v| < c * |u - v|` for all `u ≠ v`.

The witness is `f x = √(x² + 1)`.
-/

namespace RealAnalysis23

/-- The witness function `f x = √(x² + 1)`. -/
noncomputable def f (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 1)

lemma f_sq (x : ℝ) : f x ^ 2 = x ^ 2 + 1 := by
  have hx : (0:ℝ) ≤ x ^ 2 + 1 := by positivity
  simpa [f] using Real.sq_sqrt hx

lemma f_pos (x : ℝ) : 0 < f x := by
  have hx : (0:ℝ) < x ^ 2 + 1 := by positivity
  simpa [f] using Real.sqrt_pos.mpr hx

lemma f_ge_abs (x : ℝ) : |x| ≤ f x := by
  nlinarith [f_sq x, f_pos x, abs_nonneg x, sq_abs x]

/-- `f` is a strict contraction: `|f u - f v| < |u - v|` whenever `u ≠ v`. -/
lemma f_strict_contraction (u v : ℝ) (huv : u ≠ v) : |f u - f v| < |u - v| := by
  have hu := f_sq u
  have hv := f_sq v
  have hup := f_pos u
  have hvp := f_pos v
  have hne : 0 < (u - v) ^ 2 := by
    have : u - v ≠ 0 := sub_ne_zero.mpr huv
    positivity
  have hkey : 1 + u * v < f u * f v := by
    have hpos : 0 < f u * f v := by positivity
    rcases le_or_gt (1 + u * v) 0 with hle | hlt
    · linarith
    · nlinarith [hu, hv, hne]
  have hsq : (f u - f v) ^ 2 < (u - v) ^ 2 := by nlinarith [hu, hv, hkey]
  nlinarith [sq_abs (f u - f v), sq_abs (u - v), abs_nonneg (f u - f v), abs_nonneg (u - v)]

/-- No constant `c < 1` works for `f`. -/
lemma f_no_uniform_constant :
    ¬ (∃ c : ℝ, c < 1 ∧ ∀ u v : ℝ, u ≠ v → |f u - f v| < c * |u - v|) := by
  rintro ⟨c, hc, h⟩
  set n : ℝ := 1 / (1 - c) + 1 with hn
  have hc' : 0 < 1 - c := by linarith
  have hn1 : 1 < n := by
    have : 0 < 1 / (1 - c) := by positivity
    simp [hn]; linarith
  have hn0 : n ≠ 0 := by linarith
  have hkey := h n 0 hn0
  have hf0 : f 0 = 1 := by
    simp [f]
  have hfn : |n| ≤ f n := f_ge_abs n
  have habs : |n| = n := abs_of_pos (by linarith)
  have h1 : n - 1 ≤ |f n - f 0| := by
    have hstep : n - 1 ≤ f n - f 0 := by
      rw [habs] at hfn
      rw [hf0]
      linarith
    exact le_trans hstep (le_abs_self _)
  have h2 : |f n - f 0| < c * n := by
    simpa [habs] using hkey
  -- n (1 - c) ≥ 1 + (1 - c) > 1, but n - 1 < c n gives n (1 - c) < 1
  have h3 : n * (1 - c) < 1 := by nlinarith
  have h4 : 1 / (1 - c) * (1 - c) = 1 := by field_simp
  nlinarith

end RealAnalysis23

theorem real_analysis_23 :
    ∃ f : ℝ → ℝ,
      (∀ u v : ℝ, u ≠ v → |f u - f v| < |u - v|) ∧
      ¬ (∃ c : ℝ, c < 1 ∧ ∀ u v : ℝ, u ≠ v → |f u - f v| < c * |u - v|) :=
  ⟨RealAnalysis23.f, RealAnalysis23.f_strict_contraction, RealAnalysis23.f_no_uniform_constant⟩
