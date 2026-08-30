import Mathlib

open Set

/-!
# Pressley, Elementary Differential Geometry, Exercise 1.1.1

Is `γ(t) = (t², t⁴)` a parametrization of the parabola `y = x²`?

**Answer:** No, because while `t⁴ = (t²)²`, the x-coordinate `t²` is always non-negative.
Thus `γ` only parametrizes the right half `{ (x, y) | y = x² ∧ 0 ≤ x }` of the parabola.
-/

def γ (t : ℝ) : ℝ × ℝ := (t ^ 2, t ^ 4)

def parabola : Set (ℝ × ℝ) := { p : ℝ × ℝ | p.2 = p.1 ^ 2 }

def rightHalfParabola : Set (ℝ × ℝ) := { p : ℝ × ℝ | p.2 = p.1 ^ 2 ∧ 0 ≤ p.1 }

/-- The range of `γ` is strictly contained in the parabola, equal to its right half. -/
theorem range_γ_eq_rightHalfParabola : Set.range γ = rightHalfParabola := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨t, ht⟩
    dsimp [γ] at ht
    have hx : x = t ^ 2 := (Prod.ext_iff.mp ht.symm).1
    have hy : y = t ^ 4 := (Prod.ext_iff.mp ht.symm).2
    subst hx hy
    dsimp [rightHalfParabola]
    refine ⟨?_, sq_nonneg t⟩
    show t ^ 4 = (t ^ 2) ^ 2
    ring
  · rintro ⟨h_eq, hx⟩
    dsimp [rightHalfParabola] at h_eq hx
    refine ⟨Real.sqrt x, ?_⟩
    dsimp [γ]
    have h_sqrt : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
    have h_sqrt4 : (Real.sqrt x) ^ 4 = y := by
      calc (Real.sqrt x) ^ 4 = ((Real.sqrt x) ^ 2) ^ 2 := by ring
        _ = x ^ 2 := by rw [h_sqrt]
        _ = y := h_eq.symm
    exact Prod.ext h_sqrt h_sqrt4

/-- Disproof of the claim: `Set.range γ` is **not** the entire parabola `y = x²`. -/
theorem pressley_1_1_1_not_surjective : Set.range γ ≠ parabola := by
  intro h
  have h_mem : ((-1 : ℝ), (1 : ℝ)) ∈ parabola := by
    dsimp [parabola]
    ring
  rw [← h, range_γ_eq_rightHalfParabola] at h_mem
  rcases h_mem with ⟨_, hx⟩
  linarith
