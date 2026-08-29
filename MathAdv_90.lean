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
# Heat conduction in a homogeneous sphere with radially symmetric data

A homogeneous body conducts heat according to the three–dimensional heat equation
`∂U/∂t = k ΔU`.  If the temperature is a function of the distance `r` from the centre
only, i.e. `U t (x,y,z) = u t (rad x y z)` with `rad x y z = √(x² + y² + z²)`, then the
Laplacian of a radial function is `u_rr + (2/r) u_r`, so that the temperature satisfies

`∂u/∂t = k (∂²u/∂r² + (2/r) ∂u/∂r)`   for `r > 0`.

This is formalised below: `RadialHeat.laplacian_radial` computes the Laplacian (sum of the
three unmixed second partial derivatives) of a radial function, and
`RadialHeat.sphere_radial_heat_equation` deduces the radial heat equation from the
three-dimensional one.
-/

namespace RadialHeat

/-- The distance from the origin in `ℝ³`. -/
noncomputable def rad (x y z : ℝ) : ℝ := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

/-- First derivative of a one–variable slice `a ↦ f (√(a² + c))` of a radial function. -/
theorem hasDerivAt_radial_slice (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a c : ℝ)
    (h : 0 < a ^ 2 + c) :
    HasDerivAt (fun a' => f (Real.sqrt (a' ^ 2 + c)))
      (deriv f (Real.sqrt (a ^ 2 + c)) * (a / Real.sqrt (a ^ 2 + c))) a := by
  have h1 : HasDerivAt (fun a' : ℝ => a' ^ 2 + c) (2 * a) a := by
    simpa using ((hasDerivAt_pow 2 a).add_const c)
  have h2 : HasDerivAt (fun a' : ℝ => Real.sqrt (a' ^ 2 + c))
      (1 / (2 * Real.sqrt (a ^ 2 + c)) * (2 * a)) a :=
    (Real.hasDerivAt_sqrt (ne_of_gt h)).comp a h1
  have h3 := (hf (Real.sqrt (a ^ 2 + c))).hasDerivAt.comp a h2
  have hr : Real.sqrt (a ^ 2 + c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  convert h3 using 1
  ring

/-- Second derivative of a one–variable slice `a ↦ f (√(a² + c))` of a radial function. -/
theorem hasDerivAt_radial_slice_second (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (a c : ℝ) (h : 0 < a ^ 2 + c) :
    HasDerivAt (fun a' => deriv (fun a'' => f (Real.sqrt (a'' ^ 2 + c))) a')
      (deriv (deriv f) (Real.sqrt (a ^ 2 + c)) * (a / Real.sqrt (a ^ 2 + c)) *
          (a / Real.sqrt (a ^ 2 + c))
        + deriv f (Real.sqrt (a ^ 2 + c)) *
          ((1 * Real.sqrt (a ^ 2 + c) - a * (a / Real.sqrt (a ^ 2 + c)))
            / (Real.sqrt (a ^ 2 + c)) ^ 2)) a := by
  have hr : 0 < Real.sqrt (a ^ 2 + c) := Real.sqrt_pos.mpr h
  have hev : ∀ᶠ a' in nhds a, deriv (fun a'' => f (Real.sqrt (a'' ^ 2 + c))) a'
      = deriv f (Real.sqrt (a' ^ 2 + c)) * (a' / Real.sqrt (a' ^ 2 + c)) := by
    have hc : ContinuousAt (fun a' : ℝ => a' ^ 2 + c) a := by fun_prop
    filter_upwards [hc.eventually_const_lt h] with a' ha'
    exact (hasDerivAt_radial_slice f hf a' c ha').deriv
  have hg : HasDerivAt (fun a' : ℝ => Real.sqrt (a' ^ 2 + c)) (a / Real.sqrt (a ^ 2 + c)) a := by
    have h1 : HasDerivAt (fun a' : ℝ => a' ^ 2 + c) (2 * a) a := by
      simpa using ((hasDerivAt_pow 2 a).add_const c)
    have h2 : HasDerivAt (fun a' : ℝ => Real.sqrt (a' ^ 2 + c))
        (1 / (2 * Real.sqrt (a ^ 2 + c)) * (2 * a)) a :=
      (Real.hasDerivAt_sqrt (ne_of_gt h)).comp a h1
    have hr' : Real.sqrt (a ^ 2 + c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
    convert h2 using 1
    ring
  have hA : HasDerivAt (fun a' : ℝ => deriv f (Real.sqrt (a' ^ 2 + c)))
      (deriv (deriv f) (Real.sqrt (a ^ 2 + c)) * (a / Real.sqrt (a ^ 2 + c))) a := by
    have hcomp := (hf' (Real.sqrt (a ^ 2 + c))).hasDerivAt.comp a hg
    exact hcomp.congr_fun (fun _ => rfl) rfl
  have hB : HasDerivAt (fun a' : ℝ => a' / Real.sqrt (a' ^ 2 + c))
      ((1 * Real.sqrt (a ^ 2 + c) - a * (a / Real.sqrt (a ^ 2 + c)))
        / (Real.sqrt (a ^ 2 + c)) ^ 2) a :=
    (hasDerivAt_id a).div hg (ne_of_gt hr)
  exact (hA.mul hB).congr_of_eventuallyEq hev

/-- **The Laplacian of a radial function.**  If `f` is twice differentiable, then away from
the origin the sum of the unmixed second partial derivatives of `(x,y,z) ↦ f (√(x²+y²+z²))`
equals `f''(r) + (2/r) f'(r)`, where `r = √(x²+y²+z²)`. -/
theorem laplacian_radial (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (x y z : ℝ) (h : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    deriv (fun a => deriv (fun a' => f (rad a' y z)) a) x
      + deriv (fun a => deriv (fun a' => f (rad x a' z)) a) y
      + deriv (fun a => deriv (fun a' => f (rad x y a')) a) z
      = deriv (deriv f) (rad x y z) + (2 / rad x y z) * deriv f (rad x y z) := by
  set r := rad x y z with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr h
  have hr2 : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt h.le
  have ex : (fun a' => f (rad a' y z)) = (fun a' => f (Real.sqrt (a' ^ 2 + (y ^ 2 + z ^ 2)))) := by
    funext a'; simp only [rad]; ring_nf
  have ey : (fun a' => f (rad x a' z)) = (fun a' => f (Real.sqrt (a' ^ 2 + (x ^ 2 + z ^ 2)))) := by
    funext a'; simp only [rad]; ring_nf
  have ez : (fun a' => f (rad x y a')) = (fun a' => f (Real.sqrt (a' ^ 2 + (x ^ 2 + y ^ 2)))) := by
    funext a'; simp only [rad]; ring_nf
  have sx : Real.sqrt (x ^ 2 + (y ^ 2 + z ^ 2)) = r := by rw [hrdef, rad]; ring_nf
  have sy : Real.sqrt (y ^ 2 + (x ^ 2 + z ^ 2)) = r := by rw [hrdef, rad]; ring_nf
  have sz : Real.sqrt (z ^ 2 + (x ^ 2 + y ^ 2)) = r := by rw [hrdef, rad]; ring_nf
  have hx := (hasDerivAt_radial_slice_second f hf hf' x (y ^ 2 + z ^ 2) (by linarith)).deriv
  have hy := (hasDerivAt_radial_slice_second f hf hf' y (x ^ 2 + z ^ 2) (by linarith)).deriv
  have hz := (hasDerivAt_radial_slice_second f hf hf' z (x ^ 2 + y ^ 2) (by linarith)).deriv
  rw [ex, ey, ez, hx, hy, hz, sx, sy, sz]
  field_simp
  linear_combination (deriv f r - deriv (deriv f) r * r) * hr2

/-- **Temperature in a homogeneous sphere with radially symmetric data.**
If the temperature `U t (x,y,z) = u t (rad x y z)` depends only on the distance `r` from the
centre and satisfies the three-dimensional heat equation `∂U/∂t = k ΔU` away from the centre,
then for `r > 0`

`∂u/∂t = k (∂²u/∂r² + (2/r) ∂u/∂r)`. -/
theorem sphere_radial_heat_equation (k : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ t, Differentiable ℝ (u t)) (hu' : ∀ t, Differentiable ℝ (deriv (u t)))
    (hheat : ∀ t x y z : ℝ, 0 < x ^ 2 + y ^ 2 + z ^ 2 →
      deriv (fun s => u s (rad x y z)) t
        = k * (deriv (fun a => deriv (fun a' => u t (rad a' y z)) a) x
            + deriv (fun a => deriv (fun a' => u t (rad x a' z)) a) y
            + deriv (fun a => deriv (fun a' => u t (rad x y a')) a) z)) :
    ∀ t r : ℝ, 0 < r →
      deriv (fun s => u s r) t
        = k * (deriv (fun a => deriv (fun a' => u t a') a) r
            + (2 / r) * deriv (fun a' => u t a') r) := by
  intro t r hr
  have hpos : 0 < r ^ 2 + 0 ^ 2 + 0 ^ 2 := by positivity
  have hrad : rad r 0 0 = r := by
    simp only [rad]
    rw [show r ^ 2 + 0 ^ 2 + 0 ^ 2 = r ^ 2 by ring, Real.sqrt_sq hr.le]
  have h1 := hheat t r 0 0 hpos
  have h2 := laplacian_radial (u t) (hu t) (hu' t) r 0 0 hpos
  rw [hrad] at h1 h2
  rw [h1, h2]

/-- **The problem as stated, in three-dimensional form.**
The temperature `U t (x,y,z)` inside a homogeneous sphere obeys the heat equation
`∂U/∂t = k ΔU`.  If at every time it is a function of the distance from the centre only,
`U t (x,y,z) = u t (rad x y z)`, then the function `u` of the radial variable satisfies

`∂u/∂t = k (∂²u/∂r² + (2/r) ∂u/∂r)`   for all `r > 0`. -/
theorem temperature_of_radial_symmetry (k : ℝ) (U : ℝ → ℝ → ℝ → ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hradial : ∀ t x y z : ℝ, U t x y z = u t (rad x y z))
    (hu : ∀ t, Differentiable ℝ (u t)) (hu' : ∀ t, Differentiable ℝ (deriv (u t)))
    (hheat : ∀ t x y z : ℝ, 0 < x ^ 2 + y ^ 2 + z ^ 2 →
      deriv (fun s => U s x y z) t
        = k * (deriv (fun a => deriv (fun a' => U t a' y z) a) x
            + deriv (fun a => deriv (fun a' => U t x a' z) a) y
            + deriv (fun a => deriv (fun a' => U t x y a') a) z)) :
    ∀ t r : ℝ, 0 < r →
      deriv (fun s => u s r) t
        = k * (deriv (fun a => deriv (fun a' => u t a') a) r
            + (2 / r) * deriv (fun a' => u t a') r) := by
  refine sphere_radial_heat_equation k u hu hu' ?_
  intro t x y z h
  have e0 : (fun s => U s x y z) = (fun s => u s (rad x y z)) := by
    funext s; exact hradial s x y z
  have ex : (fun a' => U t a' y z) = (fun a' => u t (rad a' y z)) := by
    funext a'; exact hradial t a' y z
  have ey : (fun a' => U t x a' z) = (fun a' => u t (rad x a' z)) := by
    funext a'; exact hradial t x a' z
  have ez : (fun a' => U t x y a') = (fun a' => u t (rad x y a')) := by
    funext a'; exact hradial t x y a'
  have := hheat t x y z h
  rwa [e0, ex, ey, ez] at this

/-- The statement as originally posed: from the assumption that the temperature satisfies
the radial heat equation, the same equation holds. -/
theorem brown_1
    (k : ℝ)
    (u : ℝ → ℝ → ℝ)
    (_h_initial :
      ∃ u₀ : ℝ → ℝ, ∀ r : ℝ, u 0 r = u₀ r)
    (_h_homogeneous :
      0 < k)
    (_h_insulated :
      ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, deriv (fun r => u t r) R = 0)
    (h_eq :
      ∀ ⦃t r⦄, 0 < r →
        deriv (fun t => u t r) t
          = k * (
              deriv (fun r => deriv (fun r' => u t r') r) r
              + (2 / r) * deriv (fun r' => u t r') r
            )) :
    ∀ ⦃t r⦄, 0 < r →
      deriv (fun t => u t r) t
        = k * (
            deriv (fun r => deriv (fun r' => u t r') r) r
            + (2 / r) * deriv (fun r' => u t r') r
          ) := h_eq

end RadialHeat
