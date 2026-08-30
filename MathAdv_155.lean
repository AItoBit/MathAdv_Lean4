import Mathlib

/-!
# Gauss curvature of the catenoid

The catenoid is the surface in `ℝ³` parametrized by

  `σ(u,v) = (cosh u cos v, cosh u sin v, u)`.

We compute its first fundamental form `E, F, G`, its second fundamental form
`L, M, N`, and show that its Gauss curvature

  `K = (L*N - M^2) / (E*G - F^2) = det(II)/det(I)`

equals `-(cosh u)⁻⁴`.

All partial derivatives are genuine derivatives (`deriv` of the corresponding
one-variable slice, taken componentwise), and the unit normal is the normalized
cross product of the two tangent vectors.
-/

noncomputable section

open Real

namespace Catenoid

/-- Vectors in `ℝ³`, written as iterated products. -/
abbrev V3 := ℝ × ℝ × ℝ

/-- Euclidean inner product on `ℝ³`. -/
def dot3 (a b : V3) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- Cross product on `ℝ³`. -/
def cross3 (a b : V3) : V3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

/-- Euclidean norm on `ℝ³`. -/
def norm3 (a : V3) : ℝ := Real.sqrt (dot3 a a)

/-- Scalar multiple of a vector of `ℝ³`. -/
def smul3 (c : ℝ) (a : V3) : V3 := (c * a.1, c * a.2.1, c * a.2.2)

/-- The catenoid parametrization `σ(u,v) = (cosh u cos v, cosh u sin v, u)`. -/
def sigma (u v : ℝ) : V3 := (cosh u * cos v, cosh u * sin v, u)

/-- The partial derivative `σ_u`. -/
def sigmaU (u v : ℝ) : V3 :=
  (deriv (fun t => (sigma t v).1) u,
   deriv (fun t => (sigma t v).2.1) u,
   deriv (fun t => (sigma t v).2.2) u)

/-- The partial derivative `σ_v`. -/
def sigmaV (u v : ℝ) : V3 :=
  (deriv (fun t => (sigma u t).1) v,
   deriv (fun t => (sigma u t).2.1) v,
   deriv (fun t => (sigma u t).2.2) v)

/-- The second partial derivative `σ_uu`. -/
def sigmaUU (u v : ℝ) : V3 :=
  (deriv (fun t => (sigmaU t v).1) u,
   deriv (fun t => (sigmaU t v).2.1) u,
   deriv (fun t => (sigmaU t v).2.2) u)

/-- The mixed second partial derivative `σ_uv`. -/
def sigmaUV (u v : ℝ) : V3 :=
  (deriv (fun t => (sigmaU u t).1) v,
   deriv (fun t => (sigmaU u t).2.1) v,
   deriv (fun t => (sigmaU u t).2.2) v)

/-- The second partial derivative `σ_vv`. -/
def sigmaVV (u v : ℝ) : V3 :=
  (deriv (fun t => (sigmaV u t).1) v,
   deriv (fun t => (sigmaV u t).2.1) v,
   deriv (fun t => (sigmaV u t).2.2) v)

/-- The unit normal `N = (σ_u × σ_v)/‖σ_u × σ_v‖`. -/
def unitNormal (u v : ℝ) : V3 :=
  smul3 (norm3 (cross3 (sigmaU u v) (sigmaV u v)))⁻¹ (cross3 (sigmaU u v) (sigmaV u v))

/-- First fundamental form coefficient `E = σ_u · σ_u`. -/
def Ecoeff (u v : ℝ) : ℝ := dot3 (sigmaU u v) (sigmaU u v)

/-- First fundamental form coefficient `F = σ_u · σ_v`. -/
def Fcoeff (u v : ℝ) : ℝ := dot3 (sigmaU u v) (sigmaV u v)

/-- First fundamental form coefficient `G = σ_v · σ_v`. -/
def Gcoeff (u v : ℝ) : ℝ := dot3 (sigmaV u v) (sigmaV u v)

/-- Second fundamental form coefficient `L = σ_uu · N`. -/
def Lcoeff (u v : ℝ) : ℝ := dot3 (sigmaUU u v) (unitNormal u v)

/-- Second fundamental form coefficient `M = σ_uv · N`. -/
def Mcoeff (u v : ℝ) : ℝ := dot3 (sigmaUV u v) (unitNormal u v)

/-- Second fundamental form coefficient `N = σ_vv · N`. -/
def Ncoeff (u v : ℝ) : ℝ := dot3 (sigmaVV u v) (unitNormal u v)

/-- Gauss curvature `K = det(II)/det(I) = (LN - M²)/(EG - F²)`. -/
def gaussCurvature (u v : ℝ) : ℝ :=
  (Lcoeff u v * Ncoeff u v - Mcoeff u v ^ 2) /
    (Ecoeff u v * Gcoeff u v - Fcoeff u v ^ 2)

/-! ### Computation of the partial derivatives -/

lemma sigmaU_eq (u v : ℝ) : sigmaU u v = (sinh u * cos v, sinh u * sin v, 1) := by
  have h1 : deriv (fun t : ℝ => cosh t * cos v) u = sinh u * cos v :=
    ((Real.hasDerivAt_cosh u).mul_const (cos v)).deriv
  have h2 : deriv (fun t : ℝ => cosh t * sin v) u = sinh u * sin v :=
    ((Real.hasDerivAt_cosh u).mul_const (sin v)).deriv
  have h3 : deriv (fun t : ℝ => t) u = 1 := by simp
  simp only [sigmaU, sigma, Prod.mk.injEq]
  exact ⟨h1, h2, h3⟩

lemma sigmaV_eq (u v : ℝ) :
    sigmaV u v = (-(cosh u * sin v), cosh u * cos v, 0) := by
  have h1 : deriv (fun t : ℝ => cosh u * cos t) v = -(cosh u * sin v) := by
    simp [((Real.hasDerivAt_cos v).const_mul (cosh u)).deriv]
  have h2 : deriv (fun t : ℝ => cosh u * sin t) v = cosh u * cos v :=
    ((Real.hasDerivAt_sin v).const_mul (cosh u)).deriv
  have h3 : deriv (fun _ : ℝ => u) v = 0 := deriv_const v u
  simp only [sigmaV, sigma, Prod.mk.injEq]
  exact ⟨h1, h2, h3⟩

lemma sigmaUU_eq (u v : ℝ) : sigmaUU u v = (cosh u * cos v, cosh u * sin v, 0) := by
  have e1 : (fun t : ℝ => (sigmaU t v).1) = fun t : ℝ => sinh t * cos v := by
    funext t; rw [sigmaU_eq]
  have e2 : (fun t : ℝ => (sigmaU t v).2.1) = fun t : ℝ => sinh t * sin v := by
    funext t; rw [sigmaU_eq]
  have e3 : (fun t : ℝ => (sigmaU t v).2.2) = fun _ : ℝ => (1 : ℝ) := by
    funext t; rw [sigmaU_eq]
  have h1 : deriv (fun t : ℝ => sinh t * cos v) u = cosh u * cos v :=
    ((Real.hasDerivAt_sinh u).mul_const (cos v)).deriv
  have h2 : deriv (fun t : ℝ => sinh t * sin v) u = cosh u * sin v :=
    ((Real.hasDerivAt_sinh u).mul_const (sin v)).deriv
  simp only [sigmaUU, e1, e2, e3, h1, h2, deriv_const]


lemma sigmaUV_eq (u v : ℝ) :
    sigmaUV u v = (-(sinh u * sin v), sinh u * cos v, 0) := by
  have e1 : (fun t : ℝ => (sigmaU u t).1) = fun t : ℝ => sinh u * cos t := by
    funext t; rw [sigmaU_eq]
  have e2 : (fun t : ℝ => (sigmaU u t).2.1) = fun t : ℝ => sinh u * sin t := by
    funext t; rw [sigmaU_eq]
  have e3 : (fun t : ℝ => (sigmaU u t).2.2) = fun _ : ℝ => (1 : ℝ) := by
    funext t; rw [sigmaU_eq]
  have h1 : deriv (fun t : ℝ => sinh u * cos t) v = -(sinh u * sin v) := by
    simp [((Real.hasDerivAt_cos v).const_mul (sinh u)).deriv]
  have h2 : deriv (fun t : ℝ => sinh u * sin t) v = sinh u * cos v :=
    ((Real.hasDerivAt_sin v).const_mul (sinh u)).deriv
  simp only [sigmaUV, e1, e2, e3, h1, h2, deriv_const]

lemma sigmaVV_eq (u v : ℝ) :
    sigmaVV u v = (-(cosh u * cos v), -(cosh u * sin v), 0) := by
  have e1 : (fun t : ℝ => (sigmaV u t).1) = fun t : ℝ => -(cosh u * sin t) := by
    funext t; rw [sigmaV_eq]
  have e2 : (fun t : ℝ => (sigmaV u t).2.1) = fun t : ℝ => cosh u * cos t := by
    funext t; rw [sigmaV_eq]
  have e3 : (fun t : ℝ => (sigmaV u t).2.2) = fun _ : ℝ => (0 : ℝ) := by
    funext t; rw [sigmaV_eq]
  have h2 : deriv (fun t : ℝ => cosh u * cos t) v = -(cosh u * sin v) := by
    simp [((Real.hasDerivAt_cos v).const_mul (cosh u)).deriv]
  have h1 : deriv (fun t : ℝ => -(cosh u * sin t)) v = -(cosh u * cos v) :=
    (((Real.hasDerivAt_sin v).const_mul (cosh u)).neg).deriv
  simp only [sigmaVV, e1, e2, e3, h1, h2, deriv_const]

/-! ### First and second fundamental forms -/

lemma Ecoeff_eq (u v : ℝ) : Ecoeff u v = cosh u ^ 2 := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  have hch : cosh u ^ 2 - sinh u ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq u
  simp only [Ecoeff, dot3, sigmaU_eq]
  nlinarith [hpyth, hch]

lemma Fcoeff_eq (u v : ℝ) : Fcoeff u v = 0 := by
  simp only [Fcoeff, dot3, sigmaU_eq, sigmaV_eq]
  ring

lemma Gcoeff_eq (u v : ℝ) : Gcoeff u v = cosh u ^ 2 := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  simp only [Gcoeff, dot3, sigmaV_eq]
  nlinarith [hpyth]

lemma cross_eq (u v : ℝ) :
    cross3 (sigmaU u v) (sigmaV u v) =
      (-(cosh u * cos v), -(cosh u * sin v), sinh u * cosh u) := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  simp only [cross3, sigmaU_eq, sigmaV_eq, Prod.mk.injEq]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination (sinh u * cosh u) * hpyth

lemma norm_cross_eq (u v : ℝ) :
    norm3 (cross3 (sigmaU u v) (sigmaV u v)) = cosh u ^ 2 := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  have hch : cosh u ^ 2 - sinh u ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq u
  have hval : dot3 (cross3 (sigmaU u v) (sigmaV u v)) (cross3 (sigmaU u v) (sigmaV u v))
      = (cosh u ^ 2) ^ 2 := by
    simp only [dot3, cross_eq]
    nlinarith [hpyth, hch]
  rw [norm3, hval, Real.sqrt_sq (by positivity)]

lemma unitNormal_eq (u v : ℝ) :
    unitNormal u v =
      ((cosh u ^ 2)⁻¹ * -(cosh u * cos v), (cosh u ^ 2)⁻¹ * -(cosh u * sin v),
        (cosh u ^ 2)⁻¹ * (sinh u * cosh u)) := by
  rw [unitNormal, norm_cross_eq, cross_eq, smul3]

lemma Lcoeff_eq (u v : ℝ) : Lcoeff u v = -1 := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  have hc : (cosh u) ≠ 0 := ne_of_gt (Real.cosh_pos u)
  simp only [Lcoeff, dot3, sigmaUU_eq, unitNormal_eq]
  field_simp
  linear_combination (-(cosh u)) * hpyth

lemma Mcoeff_eq (u v : ℝ) : Mcoeff u v = 0 := by
  simp only [Mcoeff, dot3, sigmaUV_eq, unitNormal_eq]
  ring

lemma Ncoeff_eq (u v : ℝ) : Ncoeff u v = 1 := by
  have hpyth : cos v ^ 2 + sin v ^ 2 = 1 := Real.cos_sq_add_sin_sq v
  have hc : (cosh u) ≠ 0 := ne_of_gt (Real.cosh_pos u)
  simp only [Ncoeff, dot3, sigmaVV_eq, unitNormal_eq]
  field_simp
  linear_combination (cosh u) * hpyth

/-- **The Gauss curvature of the catenoid** `σ(u,v) = (cosh u cos v, cosh u sin v, u)`
is `K(u,v) = -(cosh u)⁻⁴`. -/
theorem gaussCurvature_catenoid (u v : ℝ) :
    gaussCurvature u v = -1 / cosh u ^ 4 := by
  have hc : (cosh u) ≠ 0 := ne_of_gt (Real.cosh_pos u)
  simp only [gaussCurvature, Lcoeff_eq, Mcoeff_eq, Ncoeff_eq, Ecoeff_eq, Fcoeff_eq,
    Gcoeff_eq]
  field_simp
  ring

/-- Restatement of the result as a statement about the curvature function
`(u, v) ↦ K(u, v)` on `ℝ × ℝ`. -/
theorem Pressley_8_1_2 (u v : ℝ) :
    (fun p : ℝ × ℝ => gaussCurvature p.1 p.2) (u, v) = -1 / cosh u ^ 4 :=
  gaussCurvature_catenoid u v

/-
The originally supplied statement

  theorem Pressley_8_1_2
    (u v : ℝ)
    (GaussCurvatureAt : (ℝ × ℝ) → ℝ) :
    GaussCurvatureAt (u, v) = - 1 / (cosh u ^ 4) := sorry

is false as stated: `GaussCurvatureAt` is a completely arbitrary function of two
real parameters, with no link to the catenoid, so it can for instance be the zero
function.  It is replaced above by the version in which the curvature function is
the Gauss curvature `det(II)/det(I)` actually computed from the catenoid
parametrization.
-/

end Catenoid
