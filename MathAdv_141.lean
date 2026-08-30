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

/-- **Bollobás 5.21.** Let `(xₙ)` be a sequence in a normed space `X` such that
`∑ₙ |f xₙ| < ∞` for every bounded linear functional `f ∈ X*`. Then there is a
constant `M ≥ 0` with `∑ₙ |f xₙ| ≤ M ‖f‖` for every `f ∈ X*`.

The proof given here applies the uniform boundedness principle (Banach–Steinhaus) on the
Banach space `X*` to the family of evaluation functionals `f ↦ f (∑_{n < N} εₙ • xₙ)`,
indexed by `N : ℕ` and by sign patterns `ε : ℕ → {±1}`; choosing the signs of `f xₙ`
turns the resulting uniform bound into the desired estimate on the partial sums. -/
theorem bollobas_5_21
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (x : ℕ → X)
  (h_summable : ∀ f : X →L[ℝ] ℝ, Summable (fun n ↦ |f (x n)|)) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ f : X →L[ℝ] ℝ, ∑' n, |f (x n)| ≤ M * ‖f‖ := by
  classical
  set y : ℕ × (ℕ → Bool) → X :=
    fun p => ∑ n ∈ Finset.range p.1, (if p.2 n then (1:ℝ) else -1) • x n with hy
  set g : ℕ × (ℕ → Bool) → (X →L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun p => NormedSpace.inclusionInDoubleDual ℝ X (y p) with hg
  have hgapp : ∀ p f, g p f
      = ∑ n ∈ Finset.range p.1, (if p.2 n then (1:ℝ) else -1) * f (x n) := by
    intro p f
    rw [hg]
    simp only [hy, map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, NormedSpace.dual_def, smul_eq_mul]
  have hpt : ∀ f : X →L[ℝ] ℝ, ∃ C, ∀ p, ‖g p f‖ ≤ C := by
    intro f
    refine ⟨∑' n, |f (x n)|, fun p => ?_⟩
    rw [Real.norm_eq_abs, hgapp]
    calc |∑ n ∈ Finset.range p.1, (if p.2 n then (1:ℝ) else -1) * f (x n)|
        ≤ ∑ n ∈ Finset.range p.1, |(if p.2 n then (1:ℝ) else -1) * f (x n)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range p.1, |f (x n)| := by
          refine Finset.sum_congr rfl fun n _ => ?_
          by_cases h : p.2 n <;> simp [h]
      _ ≤ ∑' n, |f (x n)| :=
          (h_summable f).sum_le_tsum _ (fun n _ => abs_nonneg _)
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  refine ⟨C, le_trans (norm_nonneg _) (hC (0, fun _ => true)), fun f => ?_⟩
  refine Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) (fun N => ?_)
  set p : ℕ × (ℕ → Bool) := (N, fun n => decide (0 ≤ f (x n))) with hp
  have hsum : ∑ n ∈ Finset.range N, |f (x n)| = g p f := by
    rw [hgapp]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : 0 ≤ f (x n)
    · simp [hp, h, abs_of_nonneg h]
    · simp [hp, h, abs_of_neg (not_le.mp h)]
  rw [hsum]
  calc g p f ≤ ‖g p f‖ := le_abs_self _
    _ ≤ ‖g p‖ * ‖f‖ := (g p).le_opNorm f
    _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (hC p) (norm_nonneg f)

#print axioms bollobas_5_21
