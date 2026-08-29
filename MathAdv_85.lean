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

namespace ComplexAnalysis49

open Complex intervalIntegral

/-- The integrand `f z = π * exp (π * conj z)`. -/
noncomputable def f (z : ℂ) : ℂ := (Real.pi : ℂ) * Complex.exp ((Real.pi : ℂ) * (starRingEnd ℂ) z)

/-- The contour integral of `f` over the boundary `C` of the square with vertices
`0, 1, 1 + i, i`, traversed counterclockwise.  It is computed as the sum of the four
parametrized edge integrals `∫₀¹ f (γ t) * γ' t`. -/
noncomputable def integralOverSquareBoundary : ℂ :=
    (∫ t in (0:ℝ)..1, f (t : ℂ) * 1)
  + (∫ t in (0:ℝ)..1, f (1 + (t : ℂ) * Complex.I) * Complex.I)
  + (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) + Complex.I) * (-1))
  + (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) * Complex.I) * (-Complex.I))

/-- Basic antiderivative computation: `∫₀¹ C * exp (c t) dt = C (e^c - 1)/c`. -/
lemma integral_const_mul_cexp (C c : ℂ) (hc : c ≠ 0) :
    (∫ t in (0:ℝ)..1, C * Complex.exp (c * (t : ℂ))) = C * (Complex.exp c - 1) / c := by
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  simp [mul_div_assoc]

lemma pi_ne_zero' : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

lemma exp_neg_pi_I : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

lemma edge1 : (∫ t in (0:ℝ)..1, f (t : ℂ) * 1) = Complex.exp (Real.pi : ℂ) - 1 := by
  have h : (∫ t in (0:ℝ)..1, f (t : ℂ) * 1)
      = ∫ t in (0:ℝ)..1, (Real.pi : ℂ) * Complex.exp ((Real.pi : ℂ) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp [f]
  rw [h, integral_const_mul_cexp _ _ pi_ne_zero']
  field_simp

lemma edge2 : (∫ t in (0:ℝ)..1, f (1 + (t : ℂ) * Complex.I) * Complex.I)
    = 2 * Complex.exp (Real.pi : ℂ) := by
  have hc : -((Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have h : (∫ t in (0:ℝ)..1, f (1 + (t : ℂ) * Complex.I) * Complex.I)
      = ∫ t in (0:ℝ)..1, ((Real.pi : ℂ) * Complex.I * Complex.exp (Real.pi : ℂ))
          * Complex.exp ((-((Real.pi : ℂ) * Complex.I)) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [f, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]
    rw [show (Real.pi : ℂ) * (1 + (t : ℂ) * -Complex.I)
        = (Real.pi : ℂ) + (-((Real.pi : ℂ) * Complex.I)) * (t : ℂ) from by ring,
      Complex.exp_add]
    ring
  rw [h, integral_const_mul_cexp _ _ hc, exp_neg_pi_I]
  field_simp
  ring

lemma edge3 : (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) + Complex.I) * (-1))
    = Complex.exp (Real.pi : ℂ) - 1 := by
  have hc : -(Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h : (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) + Complex.I) * (-1))
      = ∫ t in (0:ℝ)..1, (-(Real.pi : ℂ) * (Complex.exp (Real.pi : ℂ)
            * Complex.exp (-((Real.pi : ℂ) * Complex.I))))
          * Complex.exp ((-(Real.pi : ℂ)) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [f, map_add, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal]
    rw [show (Real.pi : ℂ) * (1 - (t : ℂ) + -Complex.I)
        = ((Real.pi : ℂ) + (-((Real.pi : ℂ) * Complex.I))) + (-(Real.pi : ℂ)) * (t : ℂ) from by
        ring, Complex.exp_add, Complex.exp_add]
    ring
  rw [h, integral_const_mul_cexp _ _ hc, exp_neg_pi_I, Complex.exp_neg]
  have hne : Complex.exp (Real.pi : ℂ) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

lemma edge4 : (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) * Complex.I) * (-Complex.I)) = -2 := by
  have hc : (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero]
  have h : (∫ t in (0:ℝ)..1, f ((1 - (t : ℂ)) * Complex.I) * (-Complex.I))
      = ∫ t in (0:ℝ)..1, (-((Real.pi : ℂ) * Complex.I
            * Complex.exp (-((Real.pi : ℂ) * Complex.I))))
          * Complex.exp (((Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [f, map_mul, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal]
    rw [show (Real.pi : ℂ) * ((1 - (t : ℂ)) * -Complex.I)
        = (-((Real.pi : ℂ) * Complex.I)) + ((Real.pi : ℂ) * Complex.I) * (t : ℂ) from by ring,
      Complex.exp_add]
    ring
  rw [h, integral_const_mul_cexp _ _ hc, exp_neg_pi_I, Complex.exp_pi_mul_I]
  field_simp
  norm_num

theorem question_11 :
    integralOverSquareBoundary = (4 : ℂ) * ((Real.exp Real.pi : ℝ) - 1) := by
  rw [integralOverSquareBoundary, edge1, edge2, edge3, edge4]
  push_cast [Complex.ofReal_exp]
  ring

end ComplexAnalysis49

namespace ComplexAnalysis49

/-- Multiple-choice answer: the integral is evaluated by **reparametrization** of the four
edges of the square (option (c)); `f` is not holomorphic, so the Cauchy-type theorems do not
apply. -/
def methodAnswer : Char := 'c'

end ComplexAnalysis49
