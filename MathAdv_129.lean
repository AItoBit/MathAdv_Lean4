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

open Filter Topology
open scoped InnerProductSpace

/-- **Weak sequential completeness of a Hilbert space.**
If `(u n, v)` is Cauchy in `ℂ` for every `v` in a (separable) complex Hilbert space `H`,
then there is `u_lim ∈ H` with `(u n, v) → (u_lim, v)` for every `v`.

The proof: each pointwise limit exists by completeness of `ℂ`, giving a linear functional
`L`; the uniform boundedness principle makes `L` bounded, and the Riesz representation
theorem (`InnerProductSpace.toDual`) produces the representing vector `u_lim`.
(Separability is not needed for the argument.) -/
theorem melrose_sp2009_9
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H)
    (hCauchy : ∀ v : H, CauchySeq (fun n : ℕ => (⟪u n, v⟫_ℂ : ℂ))) :
    ∃ u_lim : H, ∀ v : H,
      Filter.Tendsto (fun n : ℕ => (⟪u n, v⟫_ℂ : ℂ)) Filter.atTop (𝓝 (⟪u_lim, v⟫_ℂ : ℂ)) := by
  -- Each sequence `n ↦ ⟪u n, v⟫` converges, since `ℂ` is complete.
  choose L hL using fun v : H => cauchySeq_tendsto_of_complete (hCauchy v)
  -- The functionals `⟪u n, ·⟫` are pointwise bounded, hence uniformly bounded.
  have hbdd : ∀ v : H, ∃ C, ∀ n, ‖(innerSL ℂ (u n)) v‖ ≤ C := by
    intro v
    obtain ⟨C, hC⟩ := ((hL v).norm).bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hbdd
  have hbound : ∀ v : H, ‖L v‖ ≤ C * ‖v‖ := by
    intro v
    refine le_of_tendsto ((hL v).norm) (Eventually.of_forall fun n => ?_)
    calc ‖⟪u n, v⟫_ℂ‖ ≤ ‖innerSL ℂ (u n)‖ * ‖v‖ := (innerSL ℂ (u n)).le_opNorm v
      _ ≤ C * ‖v‖ := by gcongr; exact hC n
  -- `L` is linear.
  have hadd : ∀ v w, L (v + w) = L v + L w := by
    intro v w
    refine tendsto_nhds_unique (hL (v + w)) ?_
    simpa only [inner_add_right] using (hL v).add (hL w)
  have hsmul : ∀ (c : ℂ) (v : H), L (c • v) = c • L v := by
    intro c v
    refine tendsto_nhds_unique (hL (c • v)) ?_
    simpa only [inner_smul_right, smul_eq_mul] using (hL v).const_mul c
  let Lc : H →L[ℂ] ℂ :=
    LinearMap.mkContinuous { toFun := L, map_add' := hadd, map_smul' := hsmul } C hbound
  -- Riesz representation.
  refine ⟨(InnerProductSpace.toDual ℂ H).symm Lc, fun v => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hL v
