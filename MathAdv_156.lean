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

/-!
# Polar coordinates: `dx ∧ dy = r dr ∧ dθ`

We work on `ℝ × ℝ` with the "polar" coordinates `(r, θ)` (first and second component),
and the map

  `polarMap (r, θ) = (r cos θ, r sin θ)`

sending polar coordinates to the cartesian ones `(x, y)`.

A `1`-form on `ℝ × ℝ` is (pointwise) a linear functional `ℝ × ℝ →L[ℝ] ℝ`; the coordinate
differentials of the polar coordinates are `dr = fst` and `dθ = snd`, and the pullbacks of the
cartesian differentials `dx`, `dy` are the differentials of the components of `polarMap`.

The wedge product of two `1`-forms `α`, `β` is the alternating `2`-form
`(α ∧ β)(u, v) = α u * β v - α v * β u`, here `wedge2`.

The statement `dx ∧ dy = r · (dr ∧ dθ)` then says: for every point `p = (r, θ)` and every pair of
tangent vectors `u, v`, the pullback of `dx ∧ dy` along `polarMap` at `p` applied to `(u, v)`
equals `r * (dr ∧ dθ)(u, v)`.
-/

namespace PolarWedge

/-- The polar coordinate map `(r, θ) ↦ (r cos θ, r sin θ)`. -/
noncomputable def polarMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)

/-- The `1`-form `dr` on the `(r, θ)`-plane. -/
noncomputable def dr : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The `1`-form `dθ` on the `(r, θ)`-plane. -/
noncomputable def dth : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The wedge product of two `1`-forms, as a `2`-form:
`(α ∧ β)(u, v) = α u * β v - α v * β u`. -/
def wedge2 (a b : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ × ℝ) : ℝ := a u * b v - a v * b u

@[simp] lemma wedge2_self (a : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ × ℝ) : wedge2 a a u v = 0 := by
  simp [wedge2, mul_comm]

lemma wedge2_swap (a b : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ × ℝ) :
    wedge2 a b u v = -wedge2 b a u v := by
  simp [wedge2]; ring

/-- The pullback `polarMap^* dx` of the `1`-form `dx`, i.e. the differential of the first
component `r cos θ` of `polarMap`: it is `cos θ · dr - r sin θ · dθ`. -/
noncomputable def pullbackDx (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  Real.cos p.2 • dr - (p.1 * Real.sin p.2) • dth

/-- The pullback `polarMap^* dy` of the `1`-form `dy`, i.e. the differential of the second
component `r sin θ` of `polarMap`: it is `sin θ · dr + r cos θ · dθ`. -/
noncomputable def pullbackDy (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  Real.sin p.2 • dr + (p.1 * Real.cos p.2) • dth

/-- `dx` pulls back to `cos θ dr - r sin θ dθ`: this is the derivative of the first component
of the polar map. -/
theorem hasFDerivAt_polar_fst (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.cos q.2) (pullbackDx p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
      (-(Real.sin p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ))) p := by
    have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    simpa [Function.comp_def, neg_smul] using
      (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p hsnd
  have := h1.mul h2
  refine this.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  dsimp [pullbackDx, dr, dth]
  ring

/-- `dy` pulls back to `sin θ dr + r cos θ dθ`: this is the derivative of the second component
of the polar map. -/
theorem hasFDerivAt_polar_snd (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.sin q.2) (pullbackDy p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.2)
      ((Real.cos p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    simpa [Function.comp_def] using (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p hsnd
  have := h1.mul h2
  refine this.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  dsimp [pullbackDy, dr, dth]
  ring

/-- The derivative of the polar map at `p` has components `polarMap^* dx` and `polarMap^* dy`. -/
theorem hasFDerivAt_polarMap (p : ℝ × ℝ) :
    HasFDerivAt polarMap ((pullbackDx p).prod (pullbackDy p)) p :=
  (hasFDerivAt_polar_fst p).prodMk (hasFDerivAt_polar_snd p)

/-- **`dx ∧ dy = r dr ∧ dθ`** at the level of pullbacks of `1`-forms:
`(polarMap^* dx) ∧ (polarMap^* dy) = r · (dr ∧ dθ)`. -/
theorem wedge_pullback_eq (p u v : ℝ × ℝ) :
    wedge2 (pullbackDx p) (pullbackDy p) u v = p.1 * wedge2 dr dth u v := by
  have hpy : Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2 = 1 := Real.sin_sq_add_cos_sq p.2
  dsimp [wedge2, pullbackDx, pullbackDy, dr, dth]
  linear_combination (p.1 * (u.1 * v.2 - u.2 * v.1)) * hpy

/-- **`dx ∧ dy = r dr ∧ dθ`.**  The pullback along the polar coordinate map
`(r, θ) ↦ (r cos θ, r sin θ)` of the area form `dx ∧ dy` (evaluated on tangent vectors via the
derivative of the map) equals `r` times `dr ∧ dθ`. -/
theorem pullback_dx_wedge_dy (p u v : ℝ × ℝ) :
    wedge2 (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)
        (fderiv ℝ polarMap p u) (fderiv ℝ polarMap p v)
      = p.1 * wedge2 dr dth u v := by
  rw [(hasFDerivAt_polarMap p).fderiv]
  simpa [wedge2] using wedge_pullback_eq p u v

end PolarWedge
