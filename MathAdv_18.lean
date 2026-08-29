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

set_option grind.warning false

open Polynomial

/-- In a finite field, at least one of `-1`, `2`, `-2` is a square.

In characteristic `2` everything is a square; otherwise, if neither `-1` nor `2` is a square
then their product `-2` is, since the quadratic character is multiplicative. -/
theorem exists_sq_neg_one_or_two_or_neg_two (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ c : F, c ^ 2 = -1 ∨ c ^ 2 = 2 ∨ c ^ 2 = -2 := by
  by_cases hchar : ringChar F = 2
  · obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two hchar (-1)
    exact ⟨c, Or.inl (by rw [sq, ← hc])⟩
  · by_cases h1 : IsSquare (-1 : F)
    · obtain ⟨c, hc⟩ := h1
      exact ⟨c, Or.inl (by rw [sq, ← hc])⟩
    · by_cases h2 : IsSquare (2 : F)
      · obtain ⟨c, hc⟩ := h2
        exact ⟨c, Or.inr (Or.inl (by rw [sq, ← hc]))⟩
      · have hne : (-2 : F) ≠ 0 := neg_ne_zero.mpr (Ring.two_ne_zero hchar)
        have hchi : quadraticChar F (-2 : F) = 1 := by
          have hsplit : (-2 : F) = (-1) * 2 := by ring
          rw [hsplit, map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr h1,
            quadraticChar_neg_one_iff_not_isSquare.mpr h2]
          norm_num
        obtain ⟨c, hc⟩ := (quadraticChar_one_iff_isSquare hne).mp hchi
        exact ⟨c, Or.inr (Or.inr (by rw [sq, ← hc]))⟩

/-- A monic quadratic polynomial has degree `2`. -/
theorem natDegree_monic_quadratic (F : Type) [Field F] (u v : F) :
    ((X : F[X]) ^ 2 + C u * X + C v).natDegree = 2 := by
  have h : (X : F[X]) ^ 2 + C u * X + C v = C 1 * X ^ 2 + C u * X + C v := by simp
  rw [h, natDegree_quadratic one_ne_zero]

/-- `X ^ 4 + 1` factors as a product of two quadratics over any finite field. -/
theorem X_pow_four_add_one_factors (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ f g : F[X], 0 < f.natDegree ∧ 0 < g.natDegree ∧
      f * g = (X : F[X]) ^ 4 + 1 := by
  obtain ⟨c, hc | hc | hc⟩ := exists_sq_neg_one_or_two_or_neg_two F
  · refine ⟨(X : F[X]) ^ 2 + C 0 * X + C c, (X : F[X]) ^ 2 + C 0 * X + C (-c), ?_, ?_, ?_⟩
    · rw [natDegree_monic_quadratic]; norm_num
    · rw [natDegree_monic_quadratic]; norm_num
    · have h : ((X : F[X]) ^ 2 + C 0 * X + C c) * ((X : F[X]) ^ 2 + C 0 * X + C (-c))
          = X ^ 4 + C (-(c ^ 2)) := by
        simp only [map_neg, map_pow, map_zero]; ring
      rw [h, hc]; simp
  · refine ⟨(X : F[X]) ^ 2 + C c * X + C 1, (X : F[X]) ^ 2 + C (-c) * X + C 1, ?_, ?_, ?_⟩
    · rw [natDegree_monic_quadratic]; norm_num
    · rw [natDegree_monic_quadratic]; norm_num
    · have h : ((X : F[X]) ^ 2 + C c * X + C 1) * ((X : F[X]) ^ 2 + C (-c) * X + C 1)
          = X ^ 4 + C (2 - c ^ 2) * X ^ 2 + 1 := by
        simp only [map_neg, map_pow, map_sub, map_one, map_ofNat]; ring
      rw [h, hc]; simp
  · refine ⟨(X : F[X]) ^ 2 + C c * X + C (-1), (X : F[X]) ^ 2 + C (-c) * X + C (-1), ?_, ?_, ?_⟩
    · rw [natDegree_monic_quadratic]; norm_num
    · rw [natDegree_monic_quadratic]; norm_num
    · have h : ((X : F[X]) ^ 2 + C c * X + C (-1)) * ((X : F[X]) ^ 2 + C (-c) * X + C (-1))
          = X ^ 4 + C (-(2 + c ^ 2)) * X ^ 2 + 1 := by
        simp only [map_neg, map_pow, map_add, map_one, map_ofNat]; ring
      rw [h, hc]; simp

/-- **Gallian 4.9.** `X ^ 4 + 1` is reducible over `ZMod p` for every prime `p`:
it is the product of two polynomials of positive degree. -/
theorem Gallian_19
    (p : ℕ) [hp : Fact p.Prime] :
    ∃ f g : Polynomial (ZMod p),
      0 < f.natDegree ∧ 0 < g.natDegree ∧
      f * g = ((Polynomial.X : Polynomial (ZMod p)) ^ 4 + (1 : Polynomial (ZMod p))) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Fintype (ZMod p) := ZMod.fintype p
  exact X_pow_four_add_one_factors (ZMod p)
