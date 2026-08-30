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

/-- A set `S ⊆ ℝ³` is a regular codimension-one submanifold if it is the zero set of a
smooth function whose differential is nowhere zero on `S` (i.e. `0` is a regular value). -/
def RegularCodim1Submanifold (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∃ g : (ℝ × ℝ × ℝ) → ℝ,
    ContDiff ℝ ⊤ g ∧
    S = {p | g p = 0} ∧
    ∀ p, p ∈ S → fderiv ℝ g p ≠ 0

/-- The graph of a smooth function `f : ℝ² → ℝ` is a regular submanifold of `ℝ³`
(regular value theorem applied to `g (x,y,z) = z - f (x,y)`). -/
theorem Tu_9_5
    (f : (ℝ × ℝ) → ℝ)
    (hf : ContDiff ℝ ⊤ f) :
    let graph : Set (ℝ × ℝ × ℝ) := {p | p.2.2 = f (p.1, p.2.1)}
    RegularCodim1Submanifold graph := by
  intro graph
  refine ⟨fun p => p.2.2 - f (p.1, p.2.1), ?_, ?_, ?_⟩
  · exact (contDiff_snd.comp contDiff_snd).sub
      (hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))
  · ext p
    simp [graph, sub_eq_zero]
  · intro p _
    have hL_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) p :=
      (differentiable_fst.prodMk (differentiable_fst.comp differentiable_snd)).differentiableAt
    have hf_diff : DifferentiableAt ℝ f (p.1, p.2.1) :=
      (hf.differentiable (by simp)) (p.1, p.2.1)
    have hk : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p :=
      hf_diff.comp p hL_diff
    have hh : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) p :=
      (differentiable_snd.comp differentiable_snd).differentiableAt
    have hd : fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2 - f (p.1, p.2.1)) p
        = fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) p
          - fderiv ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p := fderiv_sub hh hk
    intro hzero
    have happ : (fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2 - f (p.1, p.2.1)) p) (0, 0, 1) = 0 := by
      rw [hzero]
      rfl
    rw [hd] at happ
    have h1 : fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) p (0, 0, 1) = 1 := by
      have h_clm : (fun p : ℝ × ℝ × ℝ => p.2.2) =
          ⇑((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := rfl
      rw [h_clm, ContinuousLinearMap.fderiv]
      rfl
    have h2 : fderiv ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p (0, 0, 1) = 0 := by
      have h_chain : fderiv ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p =
          (fderiv ℝ f (p.1, p.2.1)).comp (fderiv ℝ (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) p) :=
        fderiv_comp p hf_diff hL_diff
      have hL_clm : (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) =
          ⇑((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
            ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) := rfl
      rw [h_chain, ContinuousLinearMap.comp_apply, hL_clm, ContinuousLinearMap.fderiv]
      have : ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) (0, 0, 1) = 0 := rfl
      rw [this]
      exact (fderiv ℝ f (p.1, p.2.1)).map_zero
    have happ_sub : (fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) p -
        fderiv ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p) (0, 0, 1)
        = fderiv ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) p (0, 0, 1) -
          fderiv ℝ (fun p : ℝ × ℝ × ℝ => f (p.1, p.2.1)) p (0, 0, 1) := rfl
    rw [happ_sub, h1, h2] at happ
    norm_num at happ
