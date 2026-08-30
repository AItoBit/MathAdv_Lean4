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

/-- **Bollobás 3.13.** For a set `A` in a real normed space `X` and `f₀ : A → ℝ`, there is a
functional in the closed unit ball of `X*` extending `f₀` if and only if
`|∑ a ∈ F, λ a * f₀ a| ≤ ‖∑ a ∈ F, λ a • a‖` for every finite `F ⊆ A` and every `λ`.
The nontrivial direction uses the Hahn–Banach theorem. -/
theorem bollobas_3_13
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (A : Set X) (f₀ : {x : X // x ∈ A} → ℝ) :
  (∃ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ ∀ a : {x : X // x ∈ A}, f a = f₀ a) ↔
  ∀ (F : Finset {x : X // x ∈ A}) (l : {x : X // x ∈ A} → ℝ),
    (∀ a ∉ F, l a = 0) →
    |∑ a ∈ F, l a * f₀ a| ≤ ‖∑ a ∈ F, l a • (a : X)‖ := by
  constructor
  · rintro ⟨f, hf, hfa⟩ F l _
    have hsum : ∑ a ∈ F, l a * f₀ a = f (∑ a ∈ F, l a • (a : X)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, hfa]
      rfl
    rw [hsum]
    calc |f (∑ a ∈ F, l a • (a:X))| = ‖f (∑ a ∈ F, l a • (a:X))‖ := rfl
      _ ≤ ‖f‖ * ‖∑ a ∈ F, l a • (a:X)‖ := f.le_opNorm _
      _ ≤ 1 * ‖∑ a ∈ F, l a • (a:X)‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ = ‖∑ a ∈ F, l a • (a:X)‖ := one_mul _
  · intro h
    set ι : ({x : X // x ∈ A} →₀ ℝ) →ₗ[ℝ] X :=
      Finsupp.linearCombination ℝ (fun a : {x : X // x ∈ A} => (a : X)) with hι
    set phi : ({x : X // x ∈ A} →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ f₀ with hphi
    have key : ∀ c, |phi c| ≤ ‖ι c‖ := by
      intro c
      have hc := h c.support c (fun a ha => Finsupp.notMem_support_iff.mp ha)
      simpa [hphi, hι, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] using hc
    have hker : LinearMap.ker ι ≤ LinearMap.ker phi := by
      intro c hc
      have hb := key c
      rw [LinearMap.mem_ker] at hc ⊢
      rw [hc, norm_zero] at hb
      exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    set g0 : (LinearMap.range ι) →ₗ[ℝ] ℝ :=
      ((LinearMap.ker ι).liftQ phi hker).comp
        (ι.quotKerEquivRange.symm : (LinearMap.range ι) →ₗ[ℝ] _) with hg0def
    have hg0 : ∀ c, ∀ hm : ι c ∈ LinearMap.range ι, g0 ⟨ι c, hm⟩ = phi c := by
      intro c hm
      have hsymm : (ι.quotKerEquivRange.symm ⟨ι c, hm⟩) = Submodule.Quotient.mk c := by
        apply ι.quotKerEquivRange.injective
        rw [LinearEquiv.apply_symm_apply]
        exact Subtype.ext (ι.quotKerEquivRange_apply_mk c).symm
      rw [hg0def]
      simp [hsymm]
    have hbound : ∀ x : (LinearMap.range ι), ‖g0 x‖ ≤ 1 * ‖x‖ := by
      rintro ⟨x, c, rfl⟩
      rw [one_mul, hg0 c]
      exact key c
    set f1 : (LinearMap.range ι) →L[ℝ] ℝ := g0.mkContinuous 1 hbound with hf1def
    have hf1 : ‖f1‖ ≤ 1 := g0.mkContinuous_norm_le zero_le_one hbound
    obtain ⟨g, hgext, hgnorm⟩ := Real.exists_extension_norm_eq (LinearMap.range ι) f1
    refine ⟨g, by rw [hgnorm]; exact hf1, ?_⟩
    intro a
    have hsingle : ι (Finsupp.single a (1:ℝ)) = (a : X) := by simp [hι]
    have ha : (a : X) ∈ LinearMap.range ι := ⟨Finsupp.single a 1, hsingle⟩
    have h1 := hgext ⟨(a:X), ha⟩
    have h2 : f1 ⟨(a:X), ha⟩ = f₀ a := by
      have h3 := hg0 (Finsupp.single a (1:ℝ)) (hsingle ▸ ha)
      rw [hf1def]
      simp only [LinearMap.mkContinuous_apply]
      rw [show (⟨(a:X), ha⟩ : LinearMap.range ι) = ⟨ι (Finsupp.single a (1:ℝ)), hsingle ▸ ha⟩ from
        Subtype.ext hsingle.symm, h3, hphi]
      simp
    rw [h1, h2]

#print axioms bollobas_3_13
