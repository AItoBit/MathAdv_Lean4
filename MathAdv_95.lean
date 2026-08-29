import Mathlib

/-!
# Orthogonality of the eigenfunctions `sin (αₙ r)` for the insulated sphere

For the heat problem in a sphere whose surface is insulated, separation of variables leads
to the eigenvalue condition `tan (α c) = α c`, and the radial eigenfunctions are
`r ↦ sin (α r)` on `0 < r < c`.  This file shows that these functions are pairwise
orthogonal on `(0, c)`.
-/

open Real intervalIntegral

/-- `phi` is an orthogonal family on the interval `[a, b]`. -/
def orthogonalOn (phi : ℕ → ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ {m n : ℕ}, m ≠ n →
    ∫ x in a..b, phi m x * phi n x = 0

/-- If `tan x = x` then `cos x ≠ 0` (in Lean, `tan` at a pole evaluates to `0`, and `x = 0`
is excluded since `cos 0 = 1`). -/
lemma cos_ne_zero_of_tan_eq_self {x : ℝ} (h : Real.tan x = x) : Real.cos x ≠ 0 := by
  intro hc
  have hx : x = 0 := by
    rw [Real.tan_eq_sin_div_cos, hc, div_zero] at h
    exact h.symm
  rw [hx] at hc
  simp at hc

/-- The eigenvalue equation `tan x = x` in the form `sin x = x * cos x`. -/
lemma sin_eq_self_mul_cos_of_tan_eq_self {x : ℝ} (h : Real.tan x = x) :
    Real.sin x = x * Real.cos x := by
  have hc := cos_ne_zero_of_tan_eq_self h
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hc] at h
  exact h

lemma integral_cos_mul (k c : ℝ) (hk : k ≠ 0) :
    ∫ r in (0:ℝ)..c, Real.cos (k * r) = Real.sin (k * c) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk]
  simp [div_eq_inv_mul]

lemma integral_sin_mul_sin (a b c : ℝ) (hsub : a - b ≠ 0) (hadd : a + b ≠ 0) :
    ∫ r in (0:ℝ)..c, Real.sin (a * r) * Real.sin (b * r)
      = (Real.sin ((a - b) * c) / (a - b) - Real.sin ((a + b) * c) / (a + b)) / 2 := by
  have hint : ∀ r : ℝ, Real.sin (a * r) * Real.sin (b * r)
      = (Real.cos ((a - b) * r) - Real.cos ((a + b) * r)) / 2 := by
    intro r
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  calc ∫ r in (0:ℝ)..c, Real.sin (a * r) * Real.sin (b * r)
      = ∫ r in (0:ℝ)..c, (Real.cos ((a - b) * r) - Real.cos ((a + b) * r)) / 2 := by
        exact intervalIntegral.integral_congr (fun r _ => hint r)
    _ = ((∫ r in (0:ℝ)..c, Real.cos ((a - b) * r))
          - ∫ r in (0:ℝ)..c, Real.cos ((a + b) * r)) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
        · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
        · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    _ = (Real.sin ((a - b) * c) / (a - b) - Real.sin ((a + b) * c) / (a + b)) / 2 := by
        rw [integral_cos_mul _ _ hsub, integral_cos_mul _ _ hadd]

/-- **Orthogonality of the radial eigenfunctions.**  If `a` and `b` are two distinct
nonnegative roots of `tan (x c) = x c`, then `sin (a r)` and `sin (b r)` are orthogonal
on `0 < r < c`. -/
lemma integral_sin_mul_sin_eq_zero_of_tan {a b c : ℝ}
    (ha : Real.tan (a * c) = a * c) (hb : Real.tan (b * c) = b * c)
    (hsub : a - b ≠ 0) (hadd : a + b ≠ 0) :
    ∫ r in (0:ℝ)..c, Real.sin (a * r) * Real.sin (b * r) = 0 := by
  have hA := sin_eq_self_mul_cos_of_tan_eq_self ha
  have hB := sin_eq_self_mul_cos_of_tan_eq_self hb
  have h1 : Real.sin ((a - b) * c) = (a - b) * (c * (Real.cos (a * c) * Real.cos (b * c))) := by
    rw [sub_mul, Real.sin_sub, hA, hB]; ring
  have h2 : Real.sin ((a + b) * c) = (a + b) * (c * (Real.cos (a * c) * Real.cos (b * c))) := by
    rw [add_mul, Real.sin_add, hA, hB]; ring
  rw [integral_sin_mul_sin a b c hsub hadd, h1, h2,
    mul_div_cancel_left₀ _ hsub, mul_div_cancel_left₀ _ hadd, sub_self, zero_div]

lemma integral_sin_mul_self_unit (a : ℝ) (ha : a ≠ 0) :
    ∫ r in (0:ℝ)..1, Real.sin (a * r) * Real.sin (a * r) = 1 / 2 - Real.sin (2 * a) / (4 * a) := by
  have h2a : 2 * a ≠ 0 := by simpa using ha
  have hint : ∀ r : ℝ, Real.sin (a * r) * Real.sin (a * r)
      = (1 - Real.cos (2 * a * r)) / 2 := by
    intro r
    have : (2 : ℝ) * a * r = 2 * (a * r) := by ring
    rw [this, Real.cos_two_mul']
    have hpy := Real.sin_sq_add_cos_sq (a * r)
    nlinarith [hpy]
  calc ∫ r in (0:ℝ)..1, Real.sin (a * r) * Real.sin (a * r)
      = ∫ r in (0:ℝ)..1, (1 - Real.cos (2 * a * r)) / 2 :=
        intervalIntegral.integral_congr (fun r _ => hint r)
    _ = ((∫ _ in (0:ℝ)..1, (1:ℝ)) - ∫ r in (0:ℝ)..1, Real.cos (2 * a * r)) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
        · exact _root_.intervalIntegrable_const
        · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    _ = 1 / 2 - Real.sin (2 * a) / (4 * a) := by
        rw [integral_cos_mul _ _ h2a]
        simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
        field_simp
        ring

/-- There is a nonzero root of the mixed equation `tan x = x`, lying in `(π, 3π/2)`. -/
lemma exists_tan_eq_self : ∃ x : ℝ, Real.pi < x ∧ x < 3 * Real.pi / 2 ∧ Real.tan x = x := by
  set f : ℝ → ℝ := fun x => Real.sin x - x * Real.cos x with hf
  have hcont : ContinuousOn f (Set.Icc Real.pi (3 * Real.pi / 2)) :=
    (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
  have hfa : f Real.pi = Real.pi := by simp [hf]
  have hfb : f (3 * Real.pi / 2) = -1 := by
    have h1 : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [hf]
    simp [h1, Real.sin_add, Real.cos_add]
  have hle : Real.pi ≤ 3 * Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hmem : (0:ℝ) ∈ Set.Ioo (f (3 * Real.pi / 2)) (f Real.pi) := by
    rw [hfa, hfb]
    exact ⟨by norm_num, Real.pi_pos⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' hle hcont hmem
  refine ⟨x, hx.1, hx.2, ?_⟩
  have hcos : Real.cos x < 0 := by
    refine Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_
    · nlinarith [Real.pi_pos, hx.1]
    · nlinarith [Real.pi_pos, hx.2]
  have hsin : Real.sin x = x * Real.cos x := by
    have : Real.sin x - x * Real.cos x = 0 := hfx
    linarith
  rw [Real.tan_eq_sin_div_cos, hsin, mul_div_assoc, div_self (ne_of_lt hcos), mul_one]

/-- The original statement, without any assumption that the roots `αₙ` are distinct, is false:
taking all `αₙ` equal to one fixed nonzero root gives a family that is not orthogonal. -/
theorem brown_6_not_orthogonal_without_distinctness :
    ¬ ∀ (c : ℝ), 0 < c → ∀ α : ℕ → ℝ, (∀ n, Real.tan (α n * c) = α n * c) →
      orthogonalOn (fun n r => Real.sin (α n * r)) 0 c := by
  intro H
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_tan_eq_self
  have hapos : 0 < a := lt_trans Real.pi_pos ha1
  have hne : a ≠ 0 := ne_of_gt hapos
  have h := H 1 one_pos (fun _ => a) (by simpa using fun _ : ℕ => ha3) (m := 0) (n := 1)
    (by norm_num)
  rw [integral_sin_mul_self_unit a hne] at h
  have hbound : Real.sin (2 * a) / (4 * a) < 1 / 2 := by
    have h1 : Real.sin (2 * a) ≤ 1 := Real.sin_le_one _
    have h2 : (0:ℝ) < 4 * a := by linarith
    rw [div_lt_div_iff₀ h2 (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.pi_gt_three]
  linarith

/-
Original statement (false as literally stated: nothing forces the `αₙ` to be distinct roots,
and `α ≡ a` for a fixed nonzero root `a` gives a non-orthogonal family, see
`brown_6_not_orthogonal_without_distinctness`).

theorem brown_6
    (c : ℝ)
    (hc : 0 < c)
    (α : ℕ → ℝ)
    (hα : ∀ n, Real.tan (α n * c) = α n * c) :
    orthogonalOn (fun n r => Real.sin (α n * r)) 0 c := by
  sorry
-/

/-- **The temperature problem in a sphere with insulated surface.**

The functions `r ↦ sin (αₙ r)`, where the `αₙ` are (distinct, nonnegative) roots of the
mixed eigenvalue equation `tan (α c) = α c`, form an orthogonal set on `0 < r < c`.

Modification of the original statement: the hypothesis `tan (αₙ c) = αₙ c` alone is not
enough — one must also know that the roots `αₙ` are pairwise distinct (and, to rule out
`α_m = -α_n`, that they are nonnegative, as is the case for the physical eigenvalues).
Without these assumptions the statement is false; see `brown_6_not_orthogonal_without_distinctness`
below.

The hypothesis `0 < c` was in the original statement and is kept, although the proof does not
need it. -/
theorem brown_6
    (c : ℝ)
    (hc : 0 < c)
    (α : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ α n)
    (hinj : Function.Injective α)
    (hα : ∀ n, Real.tan (α n * c) = α n * c) :
    orthogonalOn (fun n r => Real.sin (α n * r)) 0 c := by
  intro m n hmn
  have hne : α m ≠ α n := fun h => hmn (hinj h)
  have hsub : α m - α n ≠ 0 := sub_ne_zero_of_ne hne
  have hadd : α m + α n ≠ 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hn : 0 < α n := lt_of_le_of_lt (hpos m) h
      exact ne_of_gt (add_pos_of_nonneg_of_pos (hpos m) hn)
    · have hm : 0 < α m := lt_of_le_of_lt (hpos n) h
      exact ne_of_gt (add_pos_of_pos_of_nonneg hm (hpos n))
  exact integral_sin_mul_sin_eq_zero_of_tan (hα m) (hα n) hsub hadd
