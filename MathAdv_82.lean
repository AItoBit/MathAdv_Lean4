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
# An entire function omitting a nondegenerate segment is constant

The original statement below (`question_8`) is **false as stated**: it assumes nothing about
`f` (in particular not that `f` is holomorphic), and it allows the degenerate "segment"
`[a, a] = {a}`. Both defects are witnessed by explicit counterexamples
(`question_8_is_false` and `holomorphy_is_necessary`).

The corrected statement is `entire_omitting_segment_isConstant`: an entire function whose
range omits the segment `[a, b]` with `a ≠ b` is constant.

The method answering the multiple-choice question is **(b) Liouville's theorem**: after
composing `f` with a Möbius transformation carrying `[a,b]` to the ray `(-∞, 0]` and taking a
holomorphic square root on the slit plane, one obtains a bounded entire function, which
Liouville's theorem forces to be constant.
-/

/-- If `(w - a) / (w - b)` is a nonpositive real number, then `w` lies on the segment `[a,b]`. -/
theorem mem_segment_of_ratio_nonpos (a b w : ℂ) (s : ℝ) (hs : s ≤ 0) (hwb : w ≠ b)
    (heq : (w - a) / (w - b) = (s : ℂ)) : w ∈ segment ℝ a b := by
  have _hne : w - b ≠ 0 := sub_ne_zero.mpr hwb
  have key : w - a = (s : ℂ) * (w - b) := by
    field_simp at heq; linear_combination heq
  have hs1 : (0:ℝ) < 1 - s := by linarith
  refine ⟨1 - (-s/(1-s)), -s/(1-s), ?_, div_nonneg (by linarith) (by linarith), by ring, ?_⟩
  · have : -s/(1-s) ≤ 1 := by rw [div_le_one hs1]; linarith
    linarith
  · rw [Complex.real_smul, Complex.real_smul]
    push_cast
    have _hs1' : ((1:ℂ) - (s:ℂ)) ≠ 0 := by
      simp only [ne_eq, sub_eq_zero]
      intro hc
      have := congrArg Complex.re hc
      simp at this
      linarith
    field_simp
    linear_combination -key

/-- If `w` avoids the segment `[a, b]`, then the Möbius image `(w - a)/(w - b)` lies in the
slit plane `ℂ \ (-∞, 0]`. -/
theorem ratio_mem_slitPlane {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    (w - a) / (w - b) ∈ Complex.slitPlane := by
  have hwb : w ≠ b := fun h => hw (h ▸ right_mem_segment ℝ a b)
  by_contra hc
  rw [Complex.mem_slitPlane_iff] at hc
  push Not at hc
  obtain ⟨hre, him⟩ := hc
  refine hw (mem_segment_of_ratio_nonpos a b w ((w - a) / (w - b)).re hre hwb ?_)
  apply Complex.ext <;> simp [him]

/-- The principal square root `exp (log h / 2)` of a point of the slit plane has positive
real part. -/
theorem re_sqrt_pos {h : ℂ} (hh : h ∈ Complex.slitPlane) :
    0 < (Complex.exp (Complex.log h / 2)).re := by
  have _h1 : -Real.pi < h.arg := Complex.neg_pi_lt_arg h
  have _h2 : h.arg < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases Complex.mem_slitPlane_iff.mp hh with h' | h'
    · exact Or.inl h'.le
    · exact Or.inr h'
  have him : (Complex.log h / 2).im = h.arg / 2 := by
    simp [Complex.log_im]
  rw [Complex.exp_re, him]
  have _hcos : 0 < Real.cos (h.arg / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> [linarith; linarith]
  positivity

/-- **Main theorem.** An entire function whose range misses a nondegenerate segment `[a, b]`
is constant. (Proof: compose with a Möbius transformation sending `[a,b]` to `(-∞,0]`, take a
holomorphic square root on the slit plane, and apply Liouville's theorem to `1/(1 + √·)`.) -/
theorem entire_omitting_segment_isConstant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hmiss : ∃ a b : ℂ, a ≠ b ∧ ∀ z : ℂ, f z ∈ (segment ℝ a b)ᶜ) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  obtain ⟨a, b, hab, hmiss⟩ := hmiss
  -- `f` never takes the value `b`
  have hfb : ∀ z, f z - b ≠ 0 := fun z =>
    sub_ne_zero.mpr fun hc => hmiss z (hc ▸ right_mem_segment ℝ a b)
  set g : ℂ → ℂ := fun z => (f z - a) / (f z - b) with hg
  have hgslit : ∀ z, g z ∈ Complex.slitPlane := fun z => ratio_mem_slitPlane (hmiss z)
  have hgdiff : Differentiable ℂ g := fun z =>
    ((hf z).sub_const a).div ((hf z).sub_const b) (hfb z)
  -- the holomorphic square root
  set u : ℂ → ℂ := fun z => Complex.exp (Complex.log (g z) / 2) with hu
  have hudiff : Differentiable ℂ u := fun z =>
    (((Complex.differentiableAt_log (hgslit z)).comp z (hgdiff z)).div_const 2).cexp
  have hure : ∀ z, 0 < (u z).re := fun z => re_sqrt_pos (hgslit z)
  have husq : ∀ z, u z * u z = g z := by
    intro z
    rw [hu]
    simp only
    rw [← Complex.exp_add]
    have : Complex.log (g z) / 2 + Complex.log (g z) / 2 = Complex.log (g z) := by ring
    rw [this, Complex.exp_log (Complex.slitPlane_ne_zero (hgslit z))]
  -- the bounded entire function
  set G : ℂ → ℂ := fun z => (1 + u z)⁻¹ with hG
  have hne : ∀ z, 1 + u z ≠ 0 := by
    intro z hc
    have := congrArg Complex.re hc
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    have := hure z
    linarith
  have hGdiff : Differentiable ℂ G := fun z => ((hudiff z).const_add 1).inv (hne z)
  have hGbdd : ∀ z, ‖G z‖ ≤ 1 := by
    intro z
    rw [hG]
    simp only [norm_inv]
    rw [inv_le_one_iff₀]
    right
    calc (1:ℝ) ≤ (1 + u z).re := by
          have := (hure z); simp only [Complex.add_re, Complex.one_re]; linarith
      _ ≤ ‖1 + u z‖ := Complex.re_le_norm _
  -- Liouville
  have hGconst : ∀ z, G z = G 0 := by
    intro z
    refine hGdiff.apply_eq_apply_of_bounded ?_ z 0
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 1))
    rintro w ⟨y, rfl⟩
    simpa [Metric.mem_closedBall] using hGbdd y
  have huconst : ∀ z, u z = u 0 := by
    intro z
    have h1 : (1 + u z)⁻¹ = (1 + u 0)⁻¹ := hGconst z
    have := inv_injective h1
    linear_combination this
  refine ⟨f 0, fun z => ?_⟩
  have hgc : g z = g 0 := by rw [← husq, ← husq, huconst z]
  rw [hg] at hgc
  simp only at hgc
  have _h1 := hfb z
  have _h2 := hfb 0
  field_simp at hgc
  have : (a - b) * f z = (a - b) * f 0 := by linear_combination hgc
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  exact mul_left_cancel₀ hab' this

/-- The statement as originally posed is false: without a holomorphy assumption, and allowing
the degenerate segment `[a,a] = {a}`, the conclusion fails. Indeed `Complex.exp` is a
nonconstant entire function omitting the value `0`. -/
theorem question_8_is_false :
    ¬ (∀ f : ℂ → ℂ, (∃ a b : ℂ, ∀ z : ℂ, f z ∈ (segment ℝ a b)ᶜ) → ∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  intro H
  obtain ⟨c, hc⟩ := H Complex.exp ⟨0, 0, by
    intro z
    simp only [segment_same, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact Complex.exp_ne_zero z⟩
  have h1 : Complex.exp 0 = c := hc 0
  have h2 : Complex.exp (Real.pi * Complex.I) = c := hc _
  rw [Complex.exp_zero] at h1
  rw [Complex.exp_pi_mul_I] at h2
  rw [← h1] at h2
  norm_num at h2

/-- Holomorphy is genuinely needed, even for a nondegenerate segment: this (discontinuous)
function omits the segment `[0,1]` but is not constant. -/
theorem holomorphy_is_necessary :
    ¬ (∀ f : ℂ → ℂ, (∃ a b : ℂ, a ≠ b ∧ ∀ z : ℂ, f z ∈ (segment ℝ a b)ᶜ) →
      ∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  intro H
  obtain ⟨_, hc⟩ := H (fun z => if z = 0 then 5 else 6) ⟨0, 1, by norm_num, by
    intro z
    have hsub : segment ℝ (0:ℂ) 1 ⊆ Metric.closedBall (0:ℂ) 1 := by
      apply (convex_closedBall (0:ℂ) 1).segment_subset <;>
        simp [Metric.mem_closedBall]
    intro hmem
    have := hsub hmem
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at this
    by_cases hz : z = 0 <;> simp [hz] at this⟩
  have h1 := hc 0
  have h2 := hc 1
  norm_num at h1 h2
  rw [← h1] at h2
  norm_num at h2

/-- Corrected version of the originally posed `question_8`, stated under the same name and in
the same shape: the two necessary repairs are the holomorphy hypothesis `hf` on `f` and the
nondegeneracy `a ≠ b` of the omitted segment (both are unavoidable, see `question_8_is_false`
and `holomorphy_is_necessary`). -/
theorem question_8
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (∃ a b : ℂ, a ≠ b ∧ ∀ z : ℂ, f z ∈ Set.compl (segment ℝ a b)) →
    (∃ c : ℂ, ∀ z : ℂ, f z = c) :=
  fun h => entire_omitting_segment_isConstant f hf h

/-- The answer to the multiple-choice question "which theorem or method can be used?":
option (b), Liouville's theorem. -/
def question_8_answer : Char := 'b'
