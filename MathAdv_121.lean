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
# `ℓ^p` is a normed space, for `1 < p < ∞`

We formalize the statement that, for a real exponent `p` with `1 < p`, the set

`ℓ^p = { a : ℕ → ℂ | ∑' j, |a j|^p < ∞ }`

carries the structure of a normed space over `ℝ`, whose norm is
`‖a‖_p = (∑' j, |a j|^p)^(1/p)`.

The analytic content (the triangle inequality, which is exactly Minkowski's inequality
`‖a + b‖_p ≤ ‖a‖_p + ‖b‖_p`, together with absolute homogeneity and definiteness) is
provided by Mathlib's `lp` spaces; we identify `lpSpace p` with `lp (fun _ : ℕ => ℂ) p`
and transport the normed space structure along that identification.
-/

/-- The space of complex sequences that are `p`-summable. -/
def lpSpace (p : ℝ) : Type :=
  { a : ℕ → ℂ // Summable (fun j ↦ ‖a j‖ ^ p) }

/-- The `ℓ^p` norm `‖a‖_p = (∑' j, |a j|^p)^(1/p)`. -/
noncomputable def lpNorm (p : ℝ) (a : lpSpace p) : ℝ :=
  (∑' j, ‖a.1 j‖ ^ p) ^ (1 / p)

/-- For `0 < p`, membership in `lpSpace p` is the same as membership in Mathlib's
`lp (fun _ : ℕ => ℂ) (ENNReal.ofReal p)`. -/
def lpEquiv (p : ℝ) (hp : 0 < p) : lpSpace p ≃ lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p) :=
  Equiv.subtypeEquivRight (fun a => by
    rw [show (a ∈ lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p)) ↔ Memℓp a (ENNReal.ofReal p) from Iff.rfl,
      memℓp_gen_iff (by rw [ENNReal.toReal_ofReal hp.le]; exact hp),
      ENNReal.toReal_ofReal hp.le])

theorem lpFact (p : ℝ) (hp : 1 ≤ p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp⟩

/-- The normed abelian group structure on `ℓ^p`; its triangle inequality is Minkowski's
inequality. -/
noncomputable def lpNACG (p : ℝ) (hp : 1 ≤ p) : NormedAddCommGroup (lpSpace p) :=
  letI := lpFact p hp
  letI : AddCommGroup (lpSpace p) := (lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).addCommGroup
  NormedAddCommGroup.induced (lpSpace p) (lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p))
    ((lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).addEquiv)
    (lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).injective

/-- The `ℝ`-normed space structure on `ℓ^p`. -/
noncomputable def lpNS (p : ℝ) (hp : 1 ≤ p) :
    @NormedSpace ℝ (lpSpace p) _ (lpNACG p hp).toSeminormedAddCommGroup := by
  letI := lpFact p hp
  letI : AddCommGroup (lpSpace p) := (lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).addCommGroup
  letI : Module ℝ (lpSpace p) := (lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).module ℝ
  exact NormedSpace.induced ℝ (lpSpace p) (lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p))
    ((lpEquiv p (lt_of_lt_of_le zero_lt_one hp)).linearEquiv ℝ)

/-- The norm of the structure `lpNACG` is exactly `‖a‖_p = (∑' j, |a j|^p)^(1/p)`. -/
theorem lpNACG_norm (p : ℝ) (hp : 1 ≤ p) (a : lpSpace p) :
    @norm _ (lpNACG p hp).toNorm a = lpNorm p a := by
  letI := lpFact p hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have h1 : @norm _ (lpNACG p hp).toNorm a = ‖lpEquiv p hp0 a‖ := rfl
  rw [h1, lp.norm_eq_tsum_rpow (by rw [ENNReal.toReal_ofReal hp0.le]; exact hp0),
    ENNReal.toReal_ofReal hp0.le]
  rfl

/-- For `1 < p < ∞`, `ℓ^p` is a normed space over `ℝ`. -/
theorem melrose_sp2009_1
    (p : ℝ) (hp : 1 < p) :
    ∃ (_ : NormedAddCommGroup (lpSpace p))
      (_ : NormedSpace ℝ (lpSpace p)), True :=
  ⟨lpNACG p hp.le, lpNS p hp.le, trivial⟩

/-- Strengthened form of `melrose_sp2009_1`: for `1 < p < ∞`, `ℓ^p` is a normed space over `ℝ`
whose norm is precisely `‖a‖_p = (∑' j, |a j|^p)^(1/p)`. -/
theorem melrose_sp2009_1_norm
    (p : ℝ) (hp : 1 < p) :
    ∃ (_ : NormedAddCommGroup (lpSpace p))
      (_ : NormedSpace ℝ (lpSpace p)), ∀ a : lpSpace p, ‖a‖ = lpNorm p a :=
  ⟨lpNACG p hp.le, lpNS p hp.le, lpNACG_norm p hp.le⟩

/-- Minkowski's inequality for series: the triangle inequality underlying the fact that
`‖·‖_p` is a norm on `ℓ^p`. -/
theorem minkowski_tsum (p : ℝ) (hp : 1 ≤ p) (a b : ℕ → ℂ)
    (ha : Summable fun j ↦ ‖a j‖ ^ p) (hb : Summable fun j ↦ ‖b j‖ ^ p) :
    (∑' j, ‖a j + b j‖ ^ p) ^ (1 / p) ≤
      (∑' j, ‖a j‖ ^ p) ^ (1 / p) + (∑' j, ‖b j‖ ^ p) ^ (1 / p) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  haveI := lpFact p hp
  have hpt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hmem : ∀ f : ℕ → ℂ, (Summable fun j ↦ ‖f j‖ ^ p) → Memℓp f (ENNReal.ofReal p) := by
    intro f hf
    rw [memℓp_gen_iff (by rw [hpt]; exact hp0), hpt]; exact hf
  set A : lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p) := ⟨a, hmem a ha⟩ with hA
  set B : lp (fun _ : ℕ ↦ ℂ) (ENNReal.ofReal p) := ⟨b, hmem b hb⟩ with hB
  have h := norm_add_le A B
  rw [lp.norm_eq_tsum_rpow (by rw [hpt]; exact hp0),
    lp.norm_eq_tsum_rpow (by rw [hpt]; exact hp0),
    lp.norm_eq_tsum_rpow (by rw [hpt]; exact hp0), hpt] at h
  simpa [hA, hB, lp.coeFn_add] using h

/-- Nonnegativity of the `ℓ^p` norm. -/
theorem lpNorm_nonneg (p : ℝ) (a : lpSpace p) : 0 ≤ lpNorm p a :=
  Real.rpow_nonneg (tsum_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- Absolute homogeneity of the `ℓ^p` norm: `‖c • a‖_p = |c| ‖a‖_p`. -/
theorem lpNorm_smul_tsum (p : ℝ) (hp : 0 < p) (c : ℂ) (a : ℕ → ℂ) :
    (∑' j, ‖c * a j‖ ^ p) ^ (1 / p) = ‖c‖ * (∑' j, ‖a j‖ ^ p) ^ (1 / p) := by
  have h1 : ∀ j, ‖c * a j‖ ^ p = ‖c‖ ^ p * ‖a j‖ ^ p := by
    intro j
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hS : (0 : ℝ) ≤ ∑' j, ‖a j‖ ^ p :=
    tsum_nonneg (fun j ↦ Real.rpow_nonneg (norm_nonneg _) _)
  rw [tsum_congr h1, tsum_mul_left,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) hS,
    ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel (ne_of_gt hp), Real.rpow_one]

/-- Definiteness of the `ℓ^p` norm: `‖a‖_p = 0` exactly when `a = 0`. -/
theorem lpNorm_eq_zero_tsum (p : ℝ) (hp : 0 < p) (a : ℕ → ℂ)
    (ha : Summable fun j ↦ ‖a j‖ ^ p) :
    (∑' j, ‖a j‖ ^ p) ^ (1 / p) = 0 ↔ a = 0 := by
  have hnn : ∀ j, (0 : ℝ) ≤ ‖a j‖ ^ p := fun j ↦ Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · intro h
    have hS : ∑' j, ‖a j‖ ^ p = 0 := by
      by_contra hne
      have hpos : 0 < ∑' j, ‖a j‖ ^ p := lt_of_le_of_ne (tsum_nonneg hnn) (Ne.symm hne)
      exact absurd h (ne_of_gt (Real.rpow_pos_of_pos hpos _))
    funext j
    have hj : ‖a j‖ ^ p ≤ 0 := hS ▸ ha.le_tsum j (fun i _ ↦ hnn i)
    have hj0 : ‖a j‖ = 0 := by
      by_contra hne
      exact absurd (le_antisymm hj (hnn j)) (ne_of_gt (Real.rpow_pos_of_pos
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) _))
    simpa using hj0
  · intro h
    subst h
    simp [Real.zero_rpow (ne_of_gt hp), Real.zero_rpow (inv_ne_zero (ne_of_gt hp))]
