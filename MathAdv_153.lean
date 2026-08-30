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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Pressley

/-- The surface patch `σ(u,v) = (u - v, u + v, u² + v²)`. -/
def sigma (u v : ℝ) : ℝ × (ℝ × ℝ) := (u - v, u + v, u ^ 2 + v ^ 2)

/-- The partial derivative `σ_u = (1, 1, 2u)`. -/
def sigmaU (u : ℝ) : ℝ × (ℝ × ℝ) := (1, 1, 2 * u)

/-- The partial derivative `σ_v = (-1, 1, 2v)`. -/
def sigmaV (v : ℝ) : ℝ × (ℝ × ℝ) := (-1, 1, 2 * v)

/-- `σ_u` really is the derivative of `u ↦ σ(u,v)`. -/
theorem hasDerivAt_sigma_u (u v : ℝ) :
    HasDerivAt (fun t : ℝ => sigma t v) (sigmaU u) u := by
  have h1 : HasDerivAt (fun t : ℝ => t - v) 1 u := (hasDerivAt_id u).sub_const v
  have h2 : HasDerivAt (fun t : ℝ => t + v) 1 u := (hasDerivAt_id u).add_const v
  have h3 : HasDerivAt (fun t : ℝ => t ^ 2 + v ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_pow 2 u).add_const (v ^ 2))
  exact h1.prodMk (h2.prodMk h3)

/-- `σ_v` really is the derivative of `v ↦ σ(u,v)`. -/
theorem hasDerivAt_sigma_v (u v : ℝ) :
    HasDerivAt (fun t : ℝ => sigma u t) (sigmaV v) v := by
  have h1 : HasDerivAt (fun t : ℝ => u - t) (-1) v := by
    simpa using (hasDerivAt_id v).const_sub u
  have h2 : HasDerivAt (fun t : ℝ => u + t) 1 v := by
    simpa using (hasDerivAt_id v).const_add u
  have h3 : HasDerivAt (fun t : ℝ => u ^ 2 + t ^ 2) (2 * v) v := by
    simpa using ((hasDerivAt_pow 2 v).const_add (u ^ 2))
  exact h1.prodMk (h2.prodMk h3)

/-- Show that the first fundamental form of `σ(u,v) = (u-v, u+v, u²+v²)` is
`E du² + 2F du dv + G dv²` with `E = 2 + 4u²`, `F = 4uv`, `G = 2 + 4v²`,
where `E = ⟨σ_u, σ_u⟩`, `F = ⟨σ_u, σ_v⟩`, `G = ⟨σ_v, σ_v⟩`. -/
theorem Pressley_6_1_1 (u v α β : ℝ) :
  let dot (p q : ℝ × (ℝ × ℝ)) : ℝ := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2
  let smul (a : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) := (a * p.1, a * p.2.1, a * p.2.2)
  let _σ (_u _v : ℝ) : ℝ × (ℝ × ℝ) := (_u - _v, _u + _v, _u^2 + _v^2)
  let σ_u (u _v : ℝ) : ℝ × (ℝ × ℝ) := (1, 1, 2 * u)
  let σ_v (_u v : ℝ) : ℝ × (ℝ × ℝ) := (-1, 1, 2 * v)
  let E (u v : ℝ) : ℝ := dot (σ_u u v) (σ_u u v)
  let F (u v : ℝ) : ℝ := dot (σ_u u v) (σ_v u v)
  let G (u v : ℝ) : ℝ := dot (σ_v u v) (σ_v u v)
  E u v = 2 + 4 * u ^ 2 ∧
  F u v = 4 * u * v ∧
  G u v = 2 + 4 * v ^ 2 ∧
  dot (smul α (σ_u u v)) (smul α (σ_u u v))
    + 2 * dot (σ_u u v) (σ_v u v) * α * β
    + dot (smul β (σ_v u v)) (smul β (σ_v u v))
    = (E u v) * α ^ 2 + 2 * (F u v) * α * β + (G u v) * β ^ 2 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

end Pressley
