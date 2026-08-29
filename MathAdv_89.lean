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
# Poles and residues of `e^z / (z² + π²)`

The function `f z = exp z / (z ^ 2 + π ^ 2)` has exactly two poles, at `z = iπ` and
`z = -iπ`.  Both are simple (order `1`, i.e. `meromorphicOrderAt f · = -1`) and the
corresponding residues are `i / (2π)` and `-i / (2π)`.

Method (answer to the multiple-choice question): (c) Maclaurin/Taylor series — expanding the
analytic factor `e^z / (z ± iπ)` in a power series about the pole produces the Laurent series
of `f`, whose `(z ∓ iπ)⁻¹`-coefficient is the residue.  Formally this is captured below by the
factorisations `f z = (z ∓ iπ)⁻¹ • g z` with `g` analytic and `g` nonzero at the pole.
-/

namespace ComplexAnalysis49

open Complex Filter Topology

/-- The function under study: `f z = e^z / (z² + π²)`. -/
noncomputable def f (z : ℂ) : ℂ := Complex.exp z / (z ^ 2 + (Real.pi : ℂ) ^ 2)

lemma pi_ne_zero' : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- Factorisation of the denominator: `z² + π² = (z - iπ)(z + iπ)`. -/
lemma denom_factor (z : ℂ) :
    z ^ 2 + (Real.pi : ℂ) ^ 2 = (z - Complex.I * (Real.pi : ℂ)) * (z + Complex.I * (Real.pi : ℂ)) := by
  have h : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [h]
  ring

lemma I_pi_ne_neg_I_pi : Complex.I * (Real.pi : ℂ) ≠ -(Complex.I * (Real.pi : ℂ)) := by
  intro h
  have h2 : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination h
  have := mul_eq_zero.1 h2
  rcases this with h3 | h3
  · norm_num at h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact Complex.I_ne_zero h4
    · exact pi_ne_zero' h4

/-- Away from the two poles, `(z - iπ) f z = e^z / (z + iπ)`. -/
lemma mul_sub_f (z : ℂ) (h₁ : z ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : z ≠ -(Complex.I * (Real.pi : ℂ))) :
    (z - Complex.I * (Real.pi : ℂ)) * f z = Complex.exp z / (z + Complex.I * (Real.pi : ℂ)) := by
  have hne₁ : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.2 h₁
  have hne₂ : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact h₂ (by linear_combination h)
  rw [f, denom_factor]
  field_simp

/-- Away from the two poles, `(z + iπ) f z = e^z / (z - iπ)`. -/
lemma mul_add_f (z : ℂ) (h₁ : z ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : z ≠ -(Complex.I * (Real.pi : ℂ))) :
    (z + Complex.I * (Real.pi : ℂ)) * f z = Complex.exp z / (z - Complex.I * (Real.pi : ℂ)) := by
  have hne₁ : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.2 h₁
  have hne₂ : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact h₂ (by linear_combination h)
  rw [f, denom_factor]
  field_simp

/-- `e^{iπ} = -1`. -/
lemma exp_I_pi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
  rw [mul_comm]
  exact Complex.exp_pi_mul_I

lemma exp_neg_I_pi : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
  rw [Complex.exp_neg, exp_I_pi]
  norm_num

/-- The auxiliary analytic factor at `iπ`. -/
noncomputable def gPos (z : ℂ) : ℂ := Complex.exp z / (z + Complex.I * (Real.pi : ℂ))

/-- The auxiliary analytic factor at `-iπ`. -/
noncomputable def gNeg (z : ℂ) : ℂ := Complex.exp z / (z - Complex.I * (Real.pi : ℂ))

lemma gPos_analyticAt : AnalyticAt ℂ gPos (Complex.I * (Real.pi : ℂ)) := by
  have hden : (Complex.I * (Real.pi : ℂ)) + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h
    have h2 : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact Complex.I_ne_zero h4
      · exact pi_ne_zero' h4
  exact (analyticAt_cexp).div
    (analyticAt_id.add analyticAt_const) hden

lemma gNeg_analyticAt : AnalyticAt ℂ gNeg (-(Complex.I * (Real.pi : ℂ))) := by
  have hden : (-(Complex.I * (Real.pi : ℂ))) - Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h
    have h2 : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact Complex.I_ne_zero h4
      · exact pi_ne_zero' h4
  exact (analyticAt_cexp).div
    (analyticAt_id.sub analyticAt_const) hden

/-- Value of the analytic factor at the pole `iπ`: this is the residue `i / (2π)`. -/
lemma gPos_value : gPos (Complex.I * (Real.pi : ℂ)) = Complex.I / (2 * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  rw [gPos, exp_I_pi]
  rw [div_eq_div_iff (by
      intro h
      have h2 : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact Complex.I_ne_zero h4
        · exact pi_ne_zero' h4)
    (mul_ne_zero two_ne_zero hpi)]
  have h : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-2 * (Real.pi : ℂ)) * h

/-- Value of the analytic factor at the pole `-iπ`: this is the residue `-i / (2π)`. -/
lemma gNeg_value : gNeg (-(Complex.I * (Real.pi : ℂ))) = -Complex.I / (2 * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  rw [gNeg, exp_neg_I_pi]
  rw [div_eq_div_iff (by
      intro h
      have h2 : (2 : ℂ) * (Complex.I * (Real.pi : ℂ)) = 0 := by linear_combination -h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact Complex.I_ne_zero h4
        · exact pi_ne_zero' h4)
    (mul_ne_zero two_ne_zero hpi)]
  have h : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-2 * (Real.pi : ℂ)) * h

lemma gPos_value_ne_zero : gPos (Complex.I * (Real.pi : ℂ)) ≠ 0 := by
  rw [gPos_value]
  exact div_ne_zero Complex.I_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero')

lemma gNeg_value_ne_zero : gNeg (-(Complex.I * (Real.pi : ℂ))) ≠ 0 := by
  rw [gNeg_value]
  exact div_ne_zero (neg_ne_zero.2 Complex.I_ne_zero)
    (mul_ne_zero two_ne_zero pi_ne_zero')

/-- Near `iπ` (but away from it) we have `f z = (z - iπ)⁻¹ • gPos z`. -/
lemma f_eventuallyEq_pos :
    ∀ᶠ z in 𝓝[≠] (Complex.I * (Real.pi : ℂ)),
      f z = (z - Complex.I * (Real.pi : ℂ)) ^ (-1 : ℤ) • gPos z := by
  have h1 : ∀ᶠ z in 𝓝[≠] (Complex.I * (Real.pi : ℂ)), z ≠ Complex.I * (Real.pi : ℂ) :=
    eventually_mem_nhdsWithin.mono (by intro z hz; exact hz)
  have h2 : ∀ᶠ z in 𝓝[≠] (Complex.I * (Real.pi : ℂ)), z ≠ -(Complex.I * (Real.pi : ℂ)) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact eventually_ne_nhds (I_pi_ne_neg_I_pi)
  filter_upwards [h1, h2] with z hz₁ hz₂
  have hne₁ : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.2 hz₁
  have := mul_sub_f z hz₁ hz₂
  rw [zpow_neg_one, smul_eq_mul, gPos, ← this]
  field_simp

/-- Near `-iπ` (but away from it) we have `f z = (z + iπ)⁻¹ • gNeg z`. -/
lemma f_eventuallyEq_neg :
    ∀ᶠ z in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))),
      f z = (z - -(Complex.I * (Real.pi : ℂ))) ^ (-1 : ℤ) • gNeg z := by
  have h1 : ∀ᶠ z in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))), z ≠ -(Complex.I * (Real.pi : ℂ)) :=
    eventually_mem_nhdsWithin.mono (by intro z hz; exact hz)
  have h2 : ∀ᶠ z in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))), z ≠ Complex.I * (Real.pi : ℂ) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact eventually_ne_nhds I_pi_ne_neg_I_pi.symm
  filter_upwards [h1, h2] with z hz₂ hz₁
  have hne₂ : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact hz₂ (by linear_combination h)
  have := mul_add_f z hz₁ hz₂
  rw [zpow_neg_one, smul_eq_mul, gNeg, ← this]
  have : z - -(Complex.I * (Real.pi : ℂ)) = z + Complex.I * (Real.pi : ℂ) := by ring
  rw [this]
  field_simp

lemma meromorphicAt_f (w : ℂ) : MeromorphicAt f w := by
  apply MeromorphicAt.div
  · exact (analyticAt_cexp).meromorphicAt
  · exact ((analyticAt_id.pow 2).add analyticAt_const).meromorphicAt

/-- **The pole at `iπ` is simple**: the meromorphic order of `f` at `iπ` is `-1`. -/
theorem order_at_I_pi : meromorphicOrderAt f (Complex.I * (Real.pi : ℂ)) = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff (meromorphicAt_f _)).2
    ⟨gPos, gPos_analyticAt, gPos_value_ne_zero, f_eventuallyEq_pos⟩

/-- **The pole at `-iπ` is simple**: the meromorphic order of `f` at `-iπ` is `-1`. -/
theorem order_at_neg_I_pi : meromorphicOrderAt f (-(Complex.I * (Real.pi : ℂ))) = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff (meromorphicAt_f _)).2
    ⟨gNeg, gNeg_analyticAt, gNeg_value_ne_zero, f_eventuallyEq_neg⟩

/-- **The residue at `iπ` is `i/(2π)`**, computed as `lim_{z → iπ} (z - iπ) f z`. -/
theorem residue_at_I_pi :
    Filter.Tendsto (fun z : ℂ => (z - Complex.I * (Real.pi : ℂ)) * f z)
      (𝓝[≠] (Complex.I * (Real.pi : ℂ))) (𝓝 (Complex.I / (2 * (Real.pi : ℂ)))) := by
  have hcont : Filter.Tendsto gPos (𝓝[≠] (Complex.I * (Real.pi : ℂ)))
      (𝓝 (Complex.I / (2 * (Real.pi : ℂ)))) := by
    have := gPos_analyticAt.continuousAt
    rw [← gPos_value]
    exact this.continuousWithinAt.tendsto
  refine hcont.congr' ?_
  have h1 : ∀ᶠ z in 𝓝[≠] (Complex.I * (Real.pi : ℂ)), z ≠ Complex.I * (Real.pi : ℂ) :=
    eventually_mem_nhdsWithin.mono (by intro z hz; exact hz)
  have h2 : ∀ᶠ z in 𝓝[≠] (Complex.I * (Real.pi : ℂ)), z ≠ -(Complex.I * (Real.pi : ℂ)) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact eventually_ne_nhds (I_pi_ne_neg_I_pi)
  filter_upwards [h1, h2] with z hz₁ hz₂
  exact (mul_sub_f z hz₁ hz₂).symm

/-- **The residue at `-iπ` is `-i/(2π)`**, computed as `lim_{z → -iπ} (z + iπ) f z`. -/
theorem residue_at_neg_I_pi :
    Filter.Tendsto (fun z : ℂ => (z + Complex.I * (Real.pi : ℂ)) * f z)
      (𝓝[≠] (-(Complex.I * (Real.pi : ℂ)))) (𝓝 (-Complex.I / (2 * (Real.pi : ℂ)))) := by
  have hcont : Filter.Tendsto gNeg (𝓝[≠] (-(Complex.I * (Real.pi : ℂ))))
      (𝓝 (-Complex.I / (2 * (Real.pi : ℂ)))) := by
    have := gNeg_analyticAt.continuousAt
    rw [← gNeg_value]
    exact this.continuousWithinAt.tendsto
  refine hcont.congr' ?_
  have h1 : ∀ᶠ z in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))), z ≠ -(Complex.I * (Real.pi : ℂ)) :=
    eventually_mem_nhdsWithin.mono (by intro z hz; exact hz)
  have h2 : ∀ᶠ z in 𝓝[≠] (-(Complex.I * (Real.pi : ℂ))), z ≠ Complex.I * (Real.pi : ℂ) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact eventually_ne_nhds I_pi_ne_neg_I_pi.symm
  filter_upwards [h1, h2] with z hz₂ hz₁
  exact (mul_add_f z hz₁ hz₂).symm

/-- The only poles are `± iπ`: elsewhere `f` is analytic. -/
theorem analyticAt_of_ne (w : ℂ) (h₁ : w ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : w ≠ -(Complex.I * (Real.pi : ℂ))) : AnalyticAt ℂ f w := by
  have hden : w ^ 2 + (Real.pi : ℂ) ^ 2 ≠ 0 := by
    rw [denom_factor]
    refine mul_ne_zero (sub_ne_zero.2 h₁) ?_
    intro h; exact h₂ (by linear_combination h)
  exact (analyticAt_cexp).div
    ((analyticAt_id.pow 2).add analyticAt_const) hden

/-- The correct partial fraction decomposition of `1 / (z² + π²)`:
the coefficients are the residues of `1 / (z² + π²)`, namely `∓ i / (2π)`. -/
theorem partial_fractions (z : ℂ) (h₁ : z ≠ Complex.I * (Real.pi : ℂ))
    (h₂ : z ≠ -(Complex.I * (Real.pi : ℂ))) :
    1 / (z ^ 2 + (Real.pi : ℂ) ^ 2)
      = (-Complex.I / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
        + (Complex.I / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ)) := by
  have hne₁ : z - Complex.I * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.2 h₁
  have hne₂ : z + Complex.I * (Real.pi : ℂ) ≠ 0 := by
    intro h; exact h₂ (by linear_combination h)
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [denom_factor]
  field_simp
  linear_combination (2 * (Real.pi : ℂ)) * hI

/-!
## The statement as originally posed is false

The originally proposed identity

`exp z / (z² + π²) = (i/(2π))/(z - iπ) + (-i/(2π))/(z + iπ)`

cannot hold: the right-hand side is a rational function, while the left-hand side is not.
(Indeed the right-hand side is `-1/(z² + π²)`, which agrees with the left-hand side only
where `exp z = -1`.)  It fails already at `z = 0`, where the left-hand side is `1/π²`
and the right-hand side is `-1/π²`.  What *is* true is that the residues of
`exp z / (z² + π²)` at its two simple poles are `± i/(2π)`, as proved above.
-/

/-- The originally proposed identity is false. -/
theorem question_15_false :
    ¬ (∀ z : ℂ,
      Complex.exp z / (z ^ 2 + (Real.pi : ℂ) ^ 2)
        =
      ((Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
        +
      (-(Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ))) := by
  intro h
  have h0 := h 0
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero'
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [Complex.exp_zero] at h0
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at h0
  have hcube : (Real.pi : ℂ) ^ 3 * 4 = 0 := by linear_combination h0 + 4 * (Real.pi : ℂ) ^ 3 * hI
  have : (Real.pi : ℂ) ^ 3 = 0 := by
    have := mul_eq_zero.1 hcube
    rcases this with h | h
    · exact h
    · norm_num at h
  exact hpi (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this)

end ComplexAnalysis49

/-
The user-provided statement (false as written; see `ComplexAnalysis49.question_15_false`):

theorem question_15 :
  ∀ z : ℂ,
    Complex.exp z / (z^2 + (Real.pi : ℂ)^2)
      =
    ((Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z - Complex.I * (Real.pi : ℂ))
      +
    (-(Complex.I : ℂ) / (2 * (Real.pi : ℂ))) / (z + Complex.I * (Real.pi : ℂ)) := by
  sorry
-/
