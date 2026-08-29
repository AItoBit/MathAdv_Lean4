import Mathlib

/-!
# Poles and residues of `(z + 1) / (z ^ 2 + 9)`

The function `f z = (z + 1) / (z ^ 2 + 9)` has two simple poles, at `z = 3i` and `z = -3i`,
with residues `(3 - i)/6` and `(3 + i)/6` respectively.  Equivalently, `f` admits the partial
fraction decomposition proved below, which exhibits both poles as simple with those residues.
-/

/-- Partial fraction decomposition of `(z + 1) / (z ^ 2 + 9)`: the poles at `± 3i` are simple
with residues `(3 ∓ i)/6`. -/
theorem question_14
  (z : ℂ)
  (hz₁ : z ≠ 3 * Complex.I)
  (hz₂ : z ≠ -3 * Complex.I) :
  (z + 1) / (z^2 + 9)
    =
  ((3 : ℂ) - Complex.I) / 6 / (z - 3 * Complex.I)
    +
  ((3 : ℂ) + Complex.I) / 6 / (z + 3 * Complex.I) := by
  have h1 : z - 3 * Complex.I ≠ 0 := sub_ne_zero.mpr hz₁
  have h2 : z + 3 * Complex.I ≠ 0 := by
    intro h
    exact hz₂ (by linear_combination h)
  have hfac : z ^ 2 + 9 = (z - 3 * Complex.I) * (z + 3 * Complex.I) := by
    have : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (9 : ℂ) * this
  rw [hfac]
  field_simp
  linear_combination (6 : ℂ) * Complex.I_sq

/-- Residue at the simple pole `z = 3i`: for a simple pole, the residue is
`lim_{z → 3i} (z - 3i) * f z = (3i + 1) / (3i + 3i) = (3 - i)/6`. -/
theorem residue_at_three_I :
    ((3 * Complex.I : ℂ) + 1) / (3 * Complex.I + 3 * Complex.I) = ((3 : ℂ) - Complex.I) / 6 := by
  have h : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  linear_combination (6 : ℂ) * Complex.I_sq

/-- Residue at the simple pole `z = -3i`: it equals
`lim_{z → -3i} (z + 3i) * f z = (-3i + 1) / (-3i - 3i) = (3 + i)/6`. -/
theorem residue_at_neg_three_I :
    ((-3 * Complex.I : ℂ) + 1) / (-3 * Complex.I - 3 * Complex.I) = ((3 : ℂ) + Complex.I) / 6 := by
  have h : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  linear_combination (6 : ℂ) * Complex.I_sq
