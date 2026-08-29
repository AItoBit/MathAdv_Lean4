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
# Heat conduction in an iron sphere with zero boundary temperature

An iron sphere with radius $R = 20\text{ cm}$, initially at uniform temperature $100^\circ\text{C}$,
is cooled with its surface kept at $0^\circ\text{C}$. Taking thermal diffusivity $k = 0.15\text{ cgs}$,
the temperature distribution is governed by the radial heat equation for a sphere:

$$\frac{\partial u}{\partial t} = k \left( \frac{\partial^2 u}{\partial r^2} + \frac{2}{r}\frac{\partial u}{\partial r} \right)$$

The accompanying multiple-choice question asks which physical model represents this problem,
with answer **(a) temperatures in a sphere**.
-/

/-- The multiple choice answer. -/
def brown_5_answer : String := "(a) temperatures in a sphere"

/-- **Problem specification (Brown & Churchill, Fourier Series and Boundary Value Problems).**
Cooling of a homogeneous sphere with radially symmetric boundary and initial conditions. -/
theorem brown_5
    (k : ℝ)
    (radius : ℝ)
    (u : ℝ → ℝ → ℝ)
    (_hk : k = 0.15)
    (_hR : radius = 20)
    (_h_initial :
      ∀ r, 0 ≤ r ∧ r ≤ radius → u 0 r = 100)
    (_h_boundary :
      ∀ t, 0 ≤ t → u t radius = 0)
    (_h_heat :
      ∀ ⦃t r⦄, 0 < r ∧ r < radius →
        deriv (fun t => u t r) t
          = k * (
              deriv (fun r => deriv (fun r' => u t r') r) r
              + (2 / r) * deriv (fun r' => u t r') r
            )) :
    True := by
  trivial
