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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
# A holomorphic function omitting a segment is constant

If `f : ℂ → ℂ` is entire and its range misses a nondegenerate segment `[a,b]`, then `f` is
constant.  The proof is by *Liouville's theorem* (answer **(b)** to the multiple-choice
question): the Möbius map `w ↦ (w - b)/(w - a)` sends `ℂ \ [a,b]` into the slit plane
`ℂ \ (-∞, 0]`, the principal square root sends the slit plane into the right half-plane,
and `s ↦ 1/(s+1)` sends the right half-plane into the unit disc.  Composing with `f` gives a
bounded entire function, which is constant by Liouville; each of the three maps is injective,
so `f` itself is constant.
-/

namespace MissingSegment

/-- The Möbius transformation `w ↦ (w - b)/(w - a)` maps the complement of the segment `[a,b]`
into the slit plane `ℂ \ (-∞, 0]`. -/
theorem moebius_mem_slitPlane_of_notMem_segment (a b w : ℂ) (hw : w ∉ segment ℝ a b) :
    (w - b) / (w - a) ∈ Complex.slitPlane := by
  have hwa : w ≠ a := fun h => hw (h ▸ left_mem_segment ℝ a b)
  have hwa' : w - a ≠ 0 := sub_ne_zero.2 hwa
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  set u : ℂ := (w - b) / (w - a) with hu
  set s : ℝ := -u.re with hs
  have hs0 : 0 ≤ s := by simp only [hs, Left.nonneg_neg_iff]; linarith
  have hueq : u = -(s : ℂ) := by
    apply Complex.ext <;> simp [hs, him]
  have hwb : w - b = u * (w - a) := by rw [hu]; field_simp
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have hc : (1 : ℂ) + (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  rw [hueq] at hwb
  have key : (s : ℂ) * a + b = w * (1 + (s : ℂ)) := by linear_combination -hwb
  exact hw ⟨s / (1 + s), 1 / (1 + s), by positivity, by positivity, by field_simp; ring, by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hc]
    linear_combination key⟩

/-- The principal square root maps the slit plane into the open right half-plane. -/
theorem re_cpow_half_pos {x : ℂ} (hx : x ∈ Complex.slitPlane) : 0 < (x ^ (1 / 2 : ℂ)).re := by
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_re]
  have h1 : (Complex.log x * (1 / 2)).im = x.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]; ring
  rw [h1]
  have h2 : |x.arg| < Real.pi :=
    abs_lt.2 ⟨Complex.neg_pi_lt_arg x, Complex.arg_lt_pi_iff.2 (hx.imp le_of_lt id)⟩
  rw [abs_lt] at h2
  have : 0 < Real.cos (x.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h2.1], by linarith [h2.2]⟩
  positivity

/-- **An entire function whose range misses a nondegenerate segment `[a,b]` is constant.**

The hypothesis `a ≠ b` is necessary: `Complex.exp` is entire and misses the degenerate segment
`[0,0] = {0}` without being constant (see `exp_missing_point_not_constant`). -/
theorem constant_of_missing_segment (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a b : ℂ) (hab : a ≠ b)
    (hmiss : ∀ z : ℂ, f z ∉ segment ℝ a b) : ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  -- `f z ≠ a` since `a` lies on the segment
  have hfa : ∀ z : ℂ, f z - a ≠ 0 := fun z =>
    sub_ne_zero.2 fun h => hmiss z (h ▸ left_mem_segment ℝ a b)
  -- the Möbius image lands in the slit plane
  set u : ℂ → ℂ := fun z => (f z - b) / (f z - a) with hudef
  have hslit : ∀ z : ℂ, u z ∈ Complex.slitPlane := fun z =>
    moebius_mem_slitPlane_of_notMem_segment a b (f z) (hmiss z)
  have hu : Differentiable ℂ u := fun z =>
    ((hf z).sub_const b).div ((hf z).sub_const a) (hfa z)
  -- its principal square root lands in the right half-plane
  set s : ℂ → ℂ := fun z => (u z) ^ (1 / 2 : ℂ) with hsdef
  have hsre : ∀ z : ℂ, 0 < (s z).re := fun z => re_cpow_half_pos (hslit z)
  have hs : Differentiable ℂ s := fun z =>
    (hu z).cpow (differentiableAt_const _) (hslit z)
  have hs1 : ∀ z : ℂ, s z + 1 ≠ 0 := by
    intro z hz
    have : (s z + 1).re = 0 := by rw [hz]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith [hsre z]
  -- the resulting bounded entire function
  set h : ℂ → ℂ := fun z => 1 / (s z + 1) with hhdef
  have hh : Differentiable ℂ h := fun z =>
    (differentiableAt_const _).div ((hs z).add_const 1) (hs1 z)
  have hbdd : Bornology.IsBounded (Set.range h) := by
    apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset
    rintro _ ⟨z, rfl⟩
    have h1 : (1 : ℝ) ≤ ‖s z + 1‖ := by
      have := Complex.re_le_norm (s z + 1)
      simp only [Complex.add_re, Complex.one_re] at this
      linarith [hsre z]
    simp only [Metric.mem_closedBall, dist_zero_right, hhdef, norm_div, norm_one]
    rw [div_le_one (by linarith)]
    exact h1
  -- Liouville
  have hconst : ∀ z w : ℂ, h z = h w := hh.apply_eq_apply_of_bounded hbdd
  refine ⟨f 0, fun z => ?_⟩
  have h1 : h z = h 0 := hconst z 0
  -- unwind the three injections
  have hs2 : s z = s 0 := by
    simp only [hhdef, one_div] at h1
    have := congrArg (fun t : ℂ => t⁻¹) h1
    simpa [inv_inv] using add_right_cancel (by simpa [inv_inv] using this : s z + 1 = s 0 + 1)
  have hpow : ∀ w : ℂ, (s w) ^ (2 : ℕ) = u w := by
    intro w
    have h2 : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
    rw [hsdef, h2]
    exact Complex.cpow_nat_inv_pow (u w) (n := 2) two_ne_zero
  have hu2 : u z = u 0 := by rw [← hpow z, ← hpow 0, hs2]
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have := hu2
  simp only [hudef, div_eq_div_iff (hfa z) (hfa 0)] at this
  have hfin : (b - a) * (f z - f 0) = 0 := by linear_combination this
  rcases mul_eq_zero.1 hfin with h' | h'
  · exact absurd h' hba
  · exact sub_eq_zero.mp h'

/-- The hypothesis `a ≠ b` cannot be dropped: `Complex.exp` is entire, omits the degenerate
segment `[0,0]`, and is not constant. -/
theorem exp_missing_point_not_constant :
    Differentiable ℂ Complex.exp ∧ (∀ z : ℂ, Complex.exp z ∉ segment ℝ (0 : ℂ) 0) ∧
      ¬ ∃ c : ℂ, ∀ z : ℂ, Complex.exp z = c := by
  refine ⟨Complex.differentiable_exp, ?_, ?_⟩
  · intro z
    simp only [segment_same, Set.mem_singleton_iff]
    exact Complex.exp_ne_zero z

  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc (Real.log 2)
    rw [Complex.exp_zero] at h0
    have : Complex.exp ((Real.log 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    rw [this] at h1
    rw [← h0] at h1
    norm_num at h1

/-!
## The statement as originally posed

The following statement, without a holomorphy assumption on `f` and without `a ≠ b`, is false;
it is recorded here (commented out) together with a disproof.

```
theorem question_8
    (f : ℂ → ℂ) :
    (∃ a b : ℂ, ∀ z : ℂ, f z ∈ Set.compl (segment ℝ a b)) →
    (∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  sorry
```
-/

/-- The literal statement of the problem, without the holomorphy hypothesis, is false: an
arbitrary (non-holomorphic) function may omit a segment without being constant. -/
theorem question_8_false :
    ¬ ∀ f : ℂ → ℂ, (∃ a b : ℂ, ∀ z : ℂ, f z ∈ Set.compl (segment ℝ a b)) →
      (∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  intro hcon
  obtain ⟨c, hc⟩ := hcon (fun z => if z = 0 then 1 else 2) ⟨0, 0, by
    intro z
    show (if z = 0 then (1 : ℂ) else 2) ∉ segment ℝ (0 : ℂ) 0
    simp only [segment_same, Set.mem_singleton_iff]
    split <;> norm_num⟩
  have h0 := hc 0
  have h1 := hc 1
  norm_num at h0 h1
  rw [← h0] at h1
  norm_num at h1

/-- Faithful formalization of the problem: an entire function omitting a nondegenerate segment
`[a,b]` (i.e. with range contained in the complement of the segment) is constant. -/
theorem question_8 (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (∃ a b : ℂ, a ≠ b ∧ ∀ z : ℂ, f z ∈ Set.compl (segment ℝ a b)) →
    (∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  rintro ⟨a, b, hab, hmiss⟩
  exact constant_of_missing_segment f hf a b hab hmiss

end MissingSegment
