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

open Complex

namespace Laplace

/-- The `ℝ`-linear identification of the plane `ℝ × ℝ` with `ℂ`, sending `(x, y)` to `x + y * I`. -/
noncomputable def toC : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (Complex.I • Complex.ofRealCLM).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma toC_apply (p : ℝ × ℝ) : toC p = (p.1 : ℂ) + (p.2 : ℂ) * I := by
  simp [toC, mul_comm]

@[simp] lemma toC_one_zero : toC (1, 0) = 1 := by simp

@[simp] lemma toC_zero_one : toC (0, 1) = I := by simp

/-- The second real iterated derivative of `(x, y) ↦ f (x + i y)`, for `f` entire, evaluated at a
pair of directions `v, w`, equals `(toC v) * (toC w)` times the second complex derivative of `f`. -/
lemma iteratedFDeriv_two_comp (f : ℂ → ℂ) (hf : Differentiable ℂ f) (p v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => f ((q.1 : ℂ) + (q.2 : ℂ) * I)) p ![v, w]
      = (toC v * toC w) • iteratedDeriv 2 f (toC p) := by
  have hcd : ContDiff ℂ (2 : ℕ) f := hf.contDiff
  have hcdR : ContDiff ℝ (2 : ℕ) f := hcd.restrict_scalars ℝ
  have hfun : (fun q : ℝ × ℝ => f ((q.1 : ℂ) + (q.2 : ℂ) * I)) = f ∘ toC := by
    funext q; simp
  rw [hfun, toC.iteratedFDeriv_comp_right hcdR p le_rfl]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [← hcd.contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  rw [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  congr 1
  simp [Fin.prod_univ_two]

/-- **Laplace's equation for holomorphic functions.**
If `f : ℂ → ℂ` is complex differentiable everywhere, then the function
`u (x, y) = f (x + i y)`, viewed as a function on the real plane, satisfies
`u_xx + u_yy = 0`: the second real iterated derivative in the direction `(1,0)` twice plus the
one in the direction `(0,1)` twice vanishes. -/
theorem strang_13_5_11 (f : ℂ → ℂ) (hf : ∀ z : ℂ, DifferentiableAt ℂ f z) :
    ∀ x y : ℝ,
      let u := fun (x y : ℝ) ↦ f (x + y * I)
      let D := iteratedFDeriv ℝ 2 (Function.uncurry u) (x, y)
      D ![(1, 0), (1, 0)] + D ![(0, 1), (0, 1)] = 0 := by
  intro x y u D
  have hfd : Differentiable ℂ f := fun z => hf z
  have hu : Function.uncurry u = fun q : ℝ × ℝ => f ((q.1 : ℂ) + (q.2 : ℂ) * I) := rfl
  have h1 : D ![(1, 0), (1, 0)] = iteratedDeriv 2 f (toC (x, y)) := by
    show iteratedFDeriv ℝ 2 (Function.uncurry u) (x, y) ![(1, 0), (1, 0)] = _
    rw [hu, iteratedFDeriv_two_comp f hfd]
    simp
  have h2 : D ![(0, 1), (0, 1)] = -iteratedDeriv 2 f (toC (x, y)) := by
    show iteratedFDeriv ℝ 2 (Function.uncurry u) (x, y) ![(0, 1), (0, 1)] = _
    rw [hu, iteratedFDeriv_two_comp f hfd]
    simp [Complex.I_mul_I]
  rw [h1, h2, add_neg_cancel]

/-!
### The literal reading of the original statement

The statement as originally written,

```
theorem strang_13_5_11
 (f : ℂ → ℂ)
  (hf : ∀ z : ℂ, DifferentiableAt ℂ f z) :
  ∀ x y : ℝ,
    let u := fun (x y : ℝ) ↦ f (x + y * I)
    let D := iteratedFDeriv ℝ 2 (Function.uncurry u) (x, y)
    D ![0, 0] + D ![1, 1] = 0
```

is *false*: there the arguments `0` and `1` are elements of `ℝ × ℝ`, i.e. the points `(0,0)` and
`(1,1)`.  Hence `D ![0,0] = 0` by multilinearity and `D ![1,1]` is the second derivative of `u` in
the diagonal direction `(1,1)`, that is `u_xx + 2 u_xy + u_yy = 2 i f''`, rather than the Laplacian
`u_xx + u_yy`.  Taking `f z = z ^ 2` gives the value `4 i ≠ 0`.  The theorem `strang_13_5_11`
above states the intended Laplace equation, evaluating the second derivative on the coordinate
directions `(1,0)` and `(0,1)`. -/
theorem strang_13_5_11_literal_false :
    ¬ (∀ (f : ℂ → ℂ), (∀ z : ℂ, DifferentiableAt ℂ f z) → ∀ x y : ℝ,
        let u := fun (x y : ℝ) ↦ f (x + y * I)
        let D := iteratedFDeriv ℝ 2 (Function.uncurry u) (x, y)
        D ![0, 0] + D ![1, 1] = 0) := by
  intro h
  have hd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := fun z => by fun_prop
  have h0 := h (fun w : ℂ => w ^ 2) hd 0 0
  simp only at h0
  have hsecond : ∀ z : ℂ, iteratedDeriv 2 (fun w : ℂ => w ^ 2) z = 2 := by
    intro z
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hderiv : deriv (fun w : ℂ => w ^ 2) = fun w => 2 * w := by funext w; simp
    rw [hderiv, deriv_const_mul_field]
    simp
  have e1 : iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * I) ^ 2)
      ((0 : ℝ), (0 : ℝ)) ![0, 0] = 0 := by
    have := iteratedFDeriv_two_comp (fun w : ℂ => w ^ 2) (fun z => hd z) (0, 0) 0 0
    simpa using this
  have e2 : iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * I) ^ 2)
      ((0 : ℝ), (0 : ℝ)) ![1, 1] = 4 * I := by
    have := iteratedFDeriv_two_comp (fun w : ℂ => w ^ 2) (fun z => hd z) (0, 0) 1 1
    rw [this, hsecond]
    have : toC (1 : ℝ × ℝ) = 1 + I := by simp
    rw [this]
    have : (1 + I) * (1 + I) = 2 * I := by ring_nf; rw [Complex.I_sq]; ring
    rw [this]
    simp [smul_eq_mul]
    ring
  rw [show (Function.uncurry fun (x y : ℝ) ↦ ((x : ℂ) + (y : ℂ) * I) ^ 2)
      = fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * I) ^ 2 from rfl] at h0
  rw [e1, e2] at h0
  simp only [zero_add] at h0
  have : (4 : ℂ) * I ≠ 0 := by simp [Complex.I_ne_zero]
  exact this h0

end Laplace
