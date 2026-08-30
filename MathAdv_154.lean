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

/-- Antiderivative for the paraboloid area integrand: `d/dr [(1+4r²)^{3/2}/12] = r√(1+4r²)`. -/
lemma hasDerivAt_paraboloid_antideriv (r : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + 4 * t ^ 2) * Real.sqrt (1 + 4 * t ^ 2) / 12)
      (r * Real.sqrt (1 + 4 * r ^ 2)) r := by
  have hu : HasDerivAt (fun t : ℝ => 1 + 4 * t ^ 2) (8 * r) r := by
    have h0 : HasDerivAt (fun t : ℝ => 1 + 4 * t ^ 2) (0 + 4 * (2 * r ^ 1)) r :=
      (hasDerivAt_const r 1).add ((hasDerivAt_pow 2 r).const_mul 4)
    convert h0 using 1
    ring
  have hpos : (0 : ℝ) < 1 + 4 * r ^ 2 := by positivity
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (1 + 4 * t ^ 2))
      (8 * r / (2 * Real.sqrt (1 + 4 * r ^ 2))) r := hu.sqrt hpos.ne'
  have h : HasDerivAt (fun t : ℝ => (1 + 4 * t ^ 2) * Real.sqrt (1 + 4 * t ^ 2) / 12)
      (((8 * r) * Real.sqrt (1 + 4 * r ^ 2) +
        (1 + 4 * r ^ 2) * (8 * r / (2 * Real.sqrt (1 + 4 * r ^ 2)))) / 12) r := by
    exact (hu.mul hs).div_const 12
  have hmul : Real.sqrt (1 + 4 * r ^ 2) * Real.sqrt (1 + 4 * r ^ 2) = 1 + 4 * r ^ 2 :=
    Real.mul_self_sqrt hpos.le
  have hne : (2 : ℝ) * Real.sqrt (1 + 4 * r ^ 2) ≠ 0 := by positivity
  have hkey : ((8 * r) * Real.sqrt (1 + 4 * r ^ 2) +
      (1 + 4 * r ^ 2) * (8 * r / (2 * Real.sqrt (1 + 4 * r ^ 2)))) / 12
      = r * Real.sqrt (1 + 4 * r ^ 2) := by
    have hterm : (1 + 4 * r ^ 2) * (8 * r / (2 * Real.sqrt (1 + 4 * r ^ 2)))
        = 4 * r * Real.sqrt (1 + 4 * r ^ 2) := by
      rw [mul_div_assoc', eq_div_iff hne]
      calc (1 + 4 * r ^ 2) * (8 * r)
          = 8 * r * (1 + 4 * r ^ 2) := by ring
        _ = 8 * r * (Real.sqrt (1 + 4 * r ^ 2) * Real.sqrt (1 + 4 * r ^ 2)) := by rw [hmul]
        _ = 4 * r * Real.sqrt (1 + 4 * r ^ 2) * (2 * Real.sqrt (1 + 4 * r ^ 2)) := by ring
    rw [hterm]
    ring
  exact hkey ▸ h

/-- The area of the part of the paraboloid `z = x² + y²` with `z ≤ 1` equals
`(π/6)(5√5 - 1)`, and the area of the lower hemisphere of the unit sphere equals `2π`,
computed via the standard surface-area integrals. -/
theorem Pressley_6_4_1 :
  let paraboloid_area_integral : ℝ :=
    ∫ _θ in (0 : ℝ)..(2 * Real.pi), ∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + 4 * r ^ 2)
  let hemisphere_area : ℝ :=
    ∫ _θ in (0 : ℝ)..(2 * Real.pi), ∫ (phi : ℝ) in (Real.pi / 2)..Real.pi, Real.sin phi
  paraboloid_area_integral = (Real.pi / 6) * (5 * Real.sqrt 5 - 1) ∧ hemisphere_area = 2 * Real.pi := by
  have hinner : (∫ r in (0 : ℝ)..1, r * Real.sqrt (1 + 4 * r ^ 2))
      = (5 * Real.sqrt 5 - 1) / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_paraboloid_antideriv x)]
    · have h5 : Real.sqrt (1 + 4 * (1 : ℝ) ^ 2) = Real.sqrt 5 := by norm_num
      have h0 : Real.sqrt (1 + 4 * (0 : ℝ) ^ 2) = 1 := by norm_num
      rw [h5, h0]
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
  have hphi : (∫ (phi : ℝ) in (Real.pi / 2)..Real.pi, Real.sin phi) = 1 := by
    rw [integral_sin]
    simp
  refine ⟨?_, ?_⟩
  · simp only [hinner, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  · simp only [hphi, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
