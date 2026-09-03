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
# Poles and residues of `f z = eᶻ / (z ² + π ²)`

The function `f z = exp z / (z ^ 2 + π ^ 2)` has exactly two singular points, `z = ± i π`.
Both are simple poles, and the corresponding residues are `B = ± i / (2 π)`.

The method used is the (Maclaurin/Taylor) expansion of the analytic function
`g z = exp z / (z ± i π)` around each pole: writing `f z = g z / (z ∓ i π)` with `g`
analytic and non-vanishing at the pole exhibits the pole as simple (order `m = 1`),
and the residue is the value `g` takes at the pole.
-/

namespace ComplexAnalysis49

open Complex Filter Topology

/-- The function under study: `f z = eᶻ / (z ^ 2 + π ^ 2)`. -/
noncomputable def f (z : ℂ) : ℂ := Complex.exp z / (z ^ 2 + (Real.pi : ℂ) ^ 2)

lemma pi_ne_zero' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-- The denominator factors as `(z - iπ) (z + iπ)`. -/
lemma denom_factor (z : ℂ) :
    z ^ 2 + (Real.pi : ℂ) ^ 2
      = (z - Complex.I * (Real.pi : ℂ)) * (z + Complex.I * (Real.pi : ℂ)) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination ((Real.pi : ℂ) ^ 2) * hI

/-- The singular points of `f` are exactly `i π` and `- i π`. -/
lemma denom_eq_zero_iff (z : ℂ) :
    z ^ 2 + (Real.pi : ℂ) ^ 2 = 0 ↔
      z = Complex.I * (Real.pi : ℂ) ∨ z = -(Complex.I * (Real.pi : ℂ)) := by
  rw [denom_factor, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

lemma I_pi_ne_neg_I_pi : Complex.I * (Real.pi : ℂ) ≠ -(Complex.I * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  intro h
  have : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination h
  simp [Complex.I_ne_zero, hpi] at this

/-- `f` is meromorphic at every point. -/
lemma meromorphicAt_f (x : ℂ) : MeromorphicAt f x :=
  (analyticAt_cexp).meromorphicAt.div
    (((analyticAt_id.pow 2).add analyticAt_const).meromorphicAt)

lemma eventually_ne_neg_I_pi :
    ∀ᶠ z : ℂ in 𝓝[≠] (Complex.I * (Real.pi : ℂ)), z ≠ -(Complex.I * (Real.pi : ℂ)) := by
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨{-(Complex.I * (Real.pi : ℂ))}ᶜ, ?_, fun z hz => hz⟩
  refine nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds ?_)
  simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using I_pi_ne_neg_I_pi

lemma eventually_ne_I_pi :
    ∀ᶠ z : ℂ in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))), z ≠ Complex.I * (Real.pi : ℂ) := by
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨{Complex.I * (Real.pi : ℂ)}ᶜ, ?_, fun z hz => hz⟩
  refine nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds ?_)
  simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using fun h => I_pi_ne_neg_I_pi h.symm

/-- Away from the two poles, `f` decomposes into partial fractions. -/
lemma f_partial_fractions {z : ℂ} (h₁ : z ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : z ≠ -(Complex.I * (Real.pi : ℂ))) :
    f z = Complex.exp z *
      ((-Complex.I / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
        + (Complex.I / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ))) := by
  have ha : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr h₁
  have hb : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact h₂ (by linear_combination h)
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [f, denom_factor]
  field_simp
  linear_combination (2 * (Real.pi : ℂ)) * hI

/-- `i π` is a pole of order `m = 1` (a simple pole) with residue `B = i / (2 π)`:
there is a function `g`, analytic and non-vanishing at `i π`, with `f z = g z / (z - i π)`
away from the singular points, and `g (i π) = i / (2 π)`. -/
lemma pole_at_I_pi :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (Complex.I * (Real.pi : ℂ)) ∧
      g (Complex.I * (Real.pi : ℂ)) = Complex.I / (2 * (Real.pi : ℂ)) ∧
      g (Complex.I * (Real.pi : ℂ)) ≠ 0 ∧
      ∀ z : ℂ, z ≠ Complex.I * (Real.pi : ℂ) → z ≠ -(Complex.I * (Real.pi : ℂ)) →
        f z = g z / (z - Complex.I * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hval : Complex.exp (Complex.I * (Real.pi : ℂ))
      / (Complex.I * (Real.pi : ℂ) + Complex.I * (Real.pi : ℂ))
      = Complex.I / (2 * (Real.pi : ℂ)) := by
    rw [mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]
    field_simp
    rw [Complex.I_sq]; ring
  have hden : Complex.I * (Real.pi : ℂ) + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact I_pi_ne_neg_I_pi (by linear_combination h)
  refine ⟨fun z => Complex.exp z / (z + Complex.I * (Real.pi : ℂ)), ?_, hval, ?_, ?_⟩
  · exact (analyticAt_cexp).div (analyticAt_id.add analyticAt_const) hden
  · show Complex.exp (Complex.I * (Real.pi : ℂ))
      / (Complex.I * (Real.pi : ℂ) + Complex.I * (Real.pi : ℂ)) ≠ 0
    rw [hval]
    simp [Complex.I_ne_zero, hpi]
  · intro z h₁ h₂
    have ha : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr h₁
    have hb : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
      intro h; exact h₂ (by linear_combination h)
    show _ = Complex.exp z / (z + Complex.I * (Real.pi : ℂ))
      / (z - Complex.I * (Real.pi : ℂ))
    rw [f, denom_factor]
    field_simp

/-- `- i π` is a pole of order `m = 1` (a simple pole) with residue `B = - i / (2 π)`. -/
lemma pole_at_neg_I_pi :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-(Complex.I * (Real.pi : ℂ))) ∧
      g (-(Complex.I * (Real.pi : ℂ))) = -Complex.I / (2 * (Real.pi : ℂ)) ∧
      g (-(Complex.I * (Real.pi : ℂ))) ≠ 0 ∧
      ∀ z : ℂ, z ≠ Complex.I * (Real.pi : ℂ) → z ≠ -(Complex.I * (Real.pi : ℂ)) →
        f z = g z / (z + Complex.I * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hval : Complex.exp (-(Complex.I * (Real.pi : ℂ)))
      / (-(Complex.I * (Real.pi : ℂ)) - Complex.I * (Real.pi : ℂ))
      = -Complex.I / (2 * (Real.pi : ℂ)) := by
    rw [show -(Complex.I * (Real.pi : ℂ)) = -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    field_simp
    rw [Complex.I_sq]; ring
  have hden : -(Complex.I * (Real.pi : ℂ)) - Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact I_pi_ne_neg_I_pi (by linear_combination -h)
  refine ⟨fun z => Complex.exp z / (z - Complex.I * (Real.pi : ℂ)), ?_, hval, ?_, ?_⟩
  · exact (analyticAt_cexp).div (analyticAt_id.sub analyticAt_const) hden
  · show Complex.exp (-(Complex.I * (Real.pi : ℂ)))
      / (-(Complex.I * (Real.pi : ℂ)) - Complex.I * (Real.pi : ℂ)) ≠ 0
    rw [hval]
    simp [Complex.I_ne_zero, hpi]
  · intro z h₁ h₂
    have ha : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr h₁
    have hb : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
      intro h; exact h₂ (by linear_combination h)
    show _ = Complex.exp z / (z - Complex.I * (Real.pi : ℂ))
      / (z + Complex.I * (Real.pi : ℂ))
    rw [f, denom_factor]
    field_simp

/-- The residue of `f` at `i π` is `B = i / (2 π)`, computed as
`lim_{z → iπ} (z - i π) f z`. -/
theorem residue_at_I_pi :
    Filter.Tendsto (fun z : ℂ => (z - Complex.I * (Real.pi : ℂ)) * f z)
      (𝓝[≠] (Complex.I * (Real.pi : ℂ))) (𝓝 (Complex.I / (2 * (Real.pi : ℂ)))) := by
  obtain ⟨g, hg, hgval, -, hfg⟩ := pole_at_I_pi
  have hmem : (fun z : ℂ => (z - Complex.I * (Real.pi : ℂ)) * f z)
      =ᶠ[𝓝[≠] (Complex.I * (Real.pi : ℂ))] g := by
    filter_upwards [eventually_ne_neg_I_pi, self_mem_nhdsWithin] with z hz hz'
    have hz'' : z ≠ Complex.I * (Real.pi : ℂ) := hz'
    rw [hfg z hz'' hz, mul_div_cancel₀ _ (sub_ne_zero.mpr hz'')]
  rw [← hgval]
  exact Filter.Tendsto.congr' hmem.symm
    (hg.continuousAt.continuousWithinAt.tendsto)

/-- The residue of `f` at `- i π` is `B = - i / (2 π)`, computed as
`lim_{z → -iπ} (z + i π) f z`. -/
theorem residue_at_neg_I_pi :
    Filter.Tendsto (fun z : ℂ => (z + Complex.I * (Real.pi : ℂ)) * f z)
      (𝓝[≠] (-(Complex.I * (Real.pi : ℂ)))) (𝓝 (-Complex.I / (2 * (Real.pi : ℂ)))) := by
  obtain ⟨g, hg, hgval, -, hfg⟩ := pole_at_neg_I_pi
  have hmem : (fun z : ℂ => (z + Complex.I * (Real.pi : ℂ)) * f z)
      =ᶠ[𝓝[≠] (-(Complex.I * (Real.pi : ℂ)))] g := by
    filter_upwards [eventually_ne_I_pi, self_mem_nhdsWithin] with z hz hz'
    have hz'' : z ≠ -(Complex.I * (Real.pi : ℂ)) := hz'
    have hb : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
      intro h; exact hz'' (by linear_combination h)
    rw [hfg z hz hz'', mul_div_cancel₀ _ hb]
  rw [← hgval]
  exact Filter.Tendsto.congr' hmem.symm
    (hg.continuousAt.continuousWithinAt.tendsto)

/-- Both poles are simple: the order of `f` at `i π` is `m = 1`, i.e. the meromorphic
order (the exponent in the leading Laurent term) equals `-1`. -/
theorem pole_order_at_I_pi :
    meromorphicOrderAt f (Complex.I * (Real.pi : ℂ)) = (-1 : ℤ) := by
  obtain ⟨g, hg, -, hgne, hfg⟩ := pole_at_I_pi
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_f _)]
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [eventually_ne_neg_I_pi, self_mem_nhdsWithin] with z hz hz'
  have hz'' : z ≠ Complex.I * (Real.pi : ℂ) := hz'
  rw [hfg z hz'' hz]
  rw [zpow_neg, zpow_one, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The order of `f` at `- i π` is `m = 1` as well. -/
theorem pole_order_at_neg_I_pi :
    meromorphicOrderAt f (-(Complex.I * (Real.pi : ℂ))) = (-1 : ℤ) := by
  obtain ⟨g, hg, -, hgne, hfg⟩ := pole_at_neg_I_pi
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_f _)]
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [eventually_ne_I_pi, self_mem_nhdsWithin] with z hz hz'
  have hz'' : z ≠ -(Complex.I * (Real.pi : ℂ)) := hz'
  rw [hfg z hz hz'']
  rw [zpow_neg, zpow_one, smul_eq_mul, div_eq_mul_inv, mul_comm, sub_neg_eq_add]

/-!
## The originally proposed identity

The statement below, which claims that `f` equals the sum of the principal parts of its
two poles, is **false**: it omits the exponential factor in the numerators (equivalently,
the entire part of the decomposition). Evaluating both sides at `z = 0` gives
`1 / π²` on the left and `-1 / π²` on the right.

```
theorem question_15 :
  ∀ z : ℂ,
    Complex.exp z / (z^2 + (Real.pi : ℂ)^2)
      =
    ((Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
      +
    (-(Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ))
```
-/

/-- The originally proposed identity is false. -/
theorem question_15_false :
    ¬ ∀ z : ℂ,
      Complex.exp z / (z ^ 2 + (Real.pi : ℂ) ^ 2)
        =
      (Complex.I / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
        +
      (-Complex.I / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ)) := by
  intro h
  have h0 := h 0
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  rw [Complex.exp_zero] at h0
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hpi2 : ((0 : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2) ≠ 0 := by
    simp [pow_ne_zero 2 hpi]
  field_simp at h0
  have h4 : (4 : ℂ) * (Real.pi : ℂ) ^ 3 = 0 := by
    linear_combination h0 + (4 * (Real.pi : ℂ) ^ 3) * hI
  simp [hpi] at h4

/-- The corrected partial-fraction identity: the residues `± i / (2 π)` appear once the
exponential factor is kept, since `e^{±iπ} = -1`. -/
theorem question_15_corrected (z : ℂ) (h₁ : z ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : z ≠ -(Complex.I * (Real.pi : ℂ))) :
    Complex.exp z / (z ^ 2 + (Real.pi : ℂ) ^ 2)
      =
    (Complex.exp (z - Complex.I * (Real.pi : ℂ)) * (Complex.I / (2 * (Real.pi : ℂ))))
        / (z - Complex.I * (Real.pi : ℂ))
      +
    (Complex.exp (z + Complex.I * (Real.pi : ℂ)) * (-Complex.I / (2 * (Real.pi : ℂ))))
        / (z + Complex.I * (Real.pi : ℂ)) := by
  have ha : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr h₁
  have hb : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact h₂ (by linear_combination h)
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have he1 : Complex.exp (z - Complex.I * (Real.pi : ℂ)) = -Complex.exp z := by
    rw [Complex.exp_sub, show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_pi_mul_I]
    ring
  have he2 : Complex.exp (z + Complex.I * (Real.pi : ℂ)) = -Complex.exp z := by
    rw [Complex.exp_add, show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_pi_mul_I]
    ring
  rw [he1, he2, denom_factor]
  field_simp
  linear_combination (2 * (Real.pi : ℂ)) * hI

end ComplexAnalysis49
