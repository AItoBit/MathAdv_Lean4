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

/-!
# Pullback of a 1-form (Tu, Problem 19.2)

Let `F : ℝ² → ℝ²` be `F (x, y) = (x² + y², x y)`.  With `u, v` the standard coordinates on the
target `ℝ²`, we show

`F* (u du + v dv) = (2x³ + 3xy²) dx + (3x²y + 2y³) dy`.

Here `ℝ²` is modelled by `EuclideanSpace ℝ (Fin 2)`, a 1-form is a (pointwise linear) assignment
`p ↦ (ω p : ℝ² →ₗ[ℝ] ℝ)`, `d f` is the differential of a function and `pullback F ω` is
`p ↦ ω (F p) ∘ dF_p`.
-/

abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- A (not necessarily smooth) 1-form on `ℝ²`. -/
abbrev OneForm := R2 → (R2 →ₗ[ℝ] ℝ)

/-- The differential of a function `f : ℝ² → ℝ`. -/
noncomputable def d (f : R2 → ℝ) : OneForm :=
  fun p => (fderiv ℝ f p).toLinearMap

/-- The pullback of a 1-form `ω` along a map `F`. -/
noncomputable def pullback (F : R2 → R2) (ω : OneForm) : OneForm :=
  fun p => (ω (F p)).comp ((fderiv ℝ F p).toLinearMap)

/-- The 1-form `dx`, i.e. the first coordinate projection at every point. -/
noncomputable def dx : OneForm :=
  fun _ => (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap

/-- The 1-form `dy`, i.e. the second coordinate projection at every point. -/
noncomputable def dy : OneForm :=
  fun _ => (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).toLinearMap

/-- Multiplication of a 1-form by a function. -/
noncomputable def smulForm (phi : R2 → ℝ) (ω : OneForm) : OneForm :=
  fun p => (phi p) • (ω p)

/-- Sum of two 1-forms. -/
noncomputable def addForm (α β : OneForm) : OneForm :=
  fun p => α p + β p

/-- The map `F (x, y) = (x² + y², x y)`. -/
def F (p : R2) : R2 :=
  !₂[p 0 ^ 2 + p 1 ^ 2, p 0 * p 1]

/-- The first standard coordinate on the target. -/
def u_coord (q : R2) : ℝ := q 0

/-- The second standard coordinate on the target. -/
def v_coord (q : R2) : ℝ := q 1

/-- The differential of `F` at `p`, as a continuous linear map. -/
noncomputable def FL (p : R2) : R2 →L[ℝ] R2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![(2 * p 0) • (EuclideanSpace.proj (𝕜 := ℝ) 0) + (2 * p 1) • (EuclideanSpace.proj (𝕜 := ℝ) 1),
        (p 1) • (EuclideanSpace.proj (𝕜 := ℝ) 0) + (p 0) • (EuclideanSpace.proj (𝕜 := ℝ) 1)])

lemma coord_hasFDerivAt (i : Fin 2) (p : R2) :
    HasFDerivAt (fun q : R2 => q i) (EuclideanSpace.proj (𝕜 := ℝ) i) p := by
  simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := p)

lemma F_hasFDerivAt (p : R2) : HasFDerivAt F (FL p) p := by
  rw [← (EuclideanSpace.equiv (Fin 2) ℝ).comp_hasFDerivAt_iff]
  have key : ((EuclideanSpace.equiv (Fin 2) ℝ : R2 →L[ℝ] (Fin 2 → ℝ)).comp (FL p)) =
      ContinuousLinearMap.pi
        ![(2 * p 0) • (EuclideanSpace.proj (𝕜 := ℝ) 0) +
            (2 * p 1) • (EuclideanSpace.proj (𝕜 := ℝ) 1),
          (p 1) • (EuclideanSpace.proj (𝕜 := ℝ) 0) +
            (p 0) • (EuclideanSpace.proj (𝕜 := ℝ) 1)] := by
    ext w i
    simp [FL]
  rw [key]
  have hcomp : (⇑(EuclideanSpace.equiv (Fin 2) ℝ) ∘ F) = fun (q : R2) (i : Fin 2) =>
      (![fun q : R2 => q 0 ^ 2 + q 1 ^ 2, fun q : R2 => q 0 * q 1] i) q := by
    funext q i
    fin_cases i <;> simp [F]
  rw [hcomp]
  refine hasFDerivAt_pi.mpr ?_
  intro i
  fin_cases i
  · exact (((coord_hasFDerivAt 0 p).pow 2).add ((coord_hasFDerivAt 1 p).pow 2)).congr_fderiv
      (by ext w; simp)
  · exact ((coord_hasFDerivAt 0 p).mul (coord_hasFDerivAt 1 p)).congr_fderiv
      (by ext w; simp; ring)

lemma fderiv_F (p : R2) : fderiv ℝ F p = FL p := (F_hasFDerivAt p).fderiv

lemma d_u_coord (q z : R2) : d u_coord q z = z 0 := by
  have : fderiv ℝ u_coord q = EuclideanSpace.proj (𝕜 := ℝ) 0 :=
    (coord_hasFDerivAt 0 q).fderiv
  simp [d, this]

lemma d_v_coord (q z : R2) : d v_coord q z = z 1 := by
  have : fderiv ℝ v_coord q = EuclideanSpace.proj (𝕜 := ℝ) 1 :=
    (coord_hasFDerivAt 1 q).fderiv
  simp [d, this]

theorem Tu_19_2 :
    pullback F (addForm (smulForm u_coord (d u_coord)) (smulForm v_coord (d v_coord))) =
      addForm
        (smulForm (fun p : R2 => 2 * p 0 ^ 3 + 3 * p 0 * p 1 ^ 2) dx)
        (smulForm (fun p : R2 => 3 * p 0 ^ 2 * p 1 + 2 * p 1 ^ 3) dy) := by
  funext p
  ext w
  simp only [pullback, addForm, smulForm, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, dx, dy, fderiv_F, d_u_coord, d_v_coord, u_coord, v_coord]
  simp [F, FL]
  ring
