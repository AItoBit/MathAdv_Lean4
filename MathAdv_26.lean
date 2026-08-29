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

open Filter Topology

/-- Given `lim_{x→8} f = -3`, `lim_{x→8} g = 5`, `lim_{x→8} h = 2`, we have
`lim_{x→8} (g x * h x - f x) = 13`, by the product and difference limit laws. -/
theorem dawkins_2_4_1c
  (f g h : ℝ → ℝ)
  (hf : Filter.Tendsto f (𝓝 8) (𝓝 (-3)))
  (hg : Filter.Tendsto g (𝓝 8) (𝓝 5))
  (hh : Filter.Tendsto h (𝓝 8) (𝓝 2)) :
  Filter.Tendsto (fun x => g x * h x - f x) (𝓝 8) (𝓝 13) := by
  have := (hg.mul hh).sub hf
  norm_num at this
  exact this
