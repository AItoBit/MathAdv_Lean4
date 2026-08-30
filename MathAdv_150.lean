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

open Real

namespace Pressley

/-- The (signed-free) curvature of a regular plane curve `γ : ℝ → ℝ × ℝ`, given by the
standard formula
`κ = |x' y'' - y' x''| / ((x')^2 + (y')^2)^(3/2)`. -/
noncomputable def planeCurvature (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  |deriv (fun s => (γ s).1) t * deriv (deriv fun s => (γ s).2) t
      - deriv (fun s => (γ s).2) t * deriv (deriv fun s => (γ s).1) t|
    / (Real.sqrt ((deriv (fun s => (γ s).1) t) ^ 2 + (deriv (fun s => (γ s).2) t) ^ 2)) ^ 3

/-- The first coordinate of the catenary `γ(t) = (t, cosh t)` has derivative `1`. -/
lemma deriv_catenary_fst : deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).1) = fun _ : ℝ => 1 := by
  simp

/-- The second coordinate of the catenary `γ(t) = (t, cosh t)` has derivative `sinh`. -/
lemma deriv_catenary_snd :
    deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).2) = Real.sinh := by
  funext t
  simp

/-- **Curvature of a graph.**  For a curve given as the graph `γ(t) = (t, f t)` of a twice
differentiable function `f`, the curvature is `|f''| / (1 + (f')^2)^(3/2)`.  (This is the
reasoning (a) applied below to `f = cosh`.) -/
lemma planeCurvature_graph (f f' f'' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (f'' x) x) (t : ℝ) :
    planeCurvature (fun t : ℝ => (t, f t)) t
      = |f'' t| / (Real.sqrt (1 + (f' t) ^ 2)) ^ 3 := by
  have h1 : deriv (fun s : ℝ => ((s, f s) : ℝ × ℝ).1) = fun _ : ℝ => 1 := by simp
  have h2 : deriv (fun s : ℝ => ((s, f s) : ℝ × ℝ).2) = f' := by
    funext x; simpa using (hf x).deriv
  simp only [planeCurvature, h1, h2, deriv_const, (hf' t).deriv, one_mul, mul_zero, sub_zero,
    one_pow]

/-- **Curvature of the catenary.**  The curve `γ(t) = (t, cosh t)` has curvature
`κ(t) = 1 / (cosh t)^2`. -/
theorem planeCurvature_catenary (t : ℝ) :
    planeCurvature (fun t : ℝ => (t, Real.cosh t)) t = 1 / (Real.cosh t) ^ 2 := by
  have hc : (0:ℝ) < Real.cosh t := Real.cosh_pos t
  have hsq : (1:ℝ) + (Real.sinh t) ^ 2 = (Real.cosh t) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  rw [planeCurvature_graph Real.cosh Real.sinh Real.cosh Real.hasDerivAt_cosh
    Real.hasDerivAt_sinh t, hsq, Real.sqrt_sq hc.le, abs_of_nonneg hc.le]
  field_simp

/-- The arc length of the catenary `γ(t) = (t, cosh t)` from `0` to `a` is `sinh a`.
The hypothesis `0 < a` is kept as stated, but it turns out to be unnecessary. -/
theorem Pressley_2_1_1 (a : ℝ) (_ha : 0 < a) :
  let γ (t : ℝ) : ℝ × ℝ := (t, cosh t)
  ∫ t in (0 : ℝ)..a, sqrt ((deriv (fun x => (γ x).1) t) ^ 2 + (deriv (fun x => (γ x).2) t) ^ 2)
    = sinh a := by
  intro γ
  have h1 : deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).1) = fun _ : ℝ => 1 :=
    deriv_catenary_fst
  have h2 : deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).2) = Real.sinh :=
    deriv_catenary_snd
  have hpt : ∀ t : ℝ,
      Real.sqrt ((deriv (fun x => (γ x).1) t) ^ 2 + (deriv (fun x => (γ x).2) t) ^ 2)
        = Real.cosh t := by
    intro t
    show Real.sqrt ((deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).1) t) ^ 2
      + (deriv (fun s : ℝ => ((s, Real.cosh s) : ℝ × ℝ).2) t) ^ 2) = Real.cosh t
    rw [h1, h2]
    have hsq : (1:ℝ) ^ 2 + (Real.sinh t) ^ 2 = (Real.cosh t) ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq t]
    rw [hsq, Real.sqrt_sq (Real.cosh_pos t).le]
  simp only [hpt]
  have : ∫ t in (0:ℝ)..a, Real.cosh t = Real.sinh a - Real.sinh 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sinh x)
      (Real.continuous_cosh.intervalIntegrable 0 a)
  simpa using this

end Pressley
