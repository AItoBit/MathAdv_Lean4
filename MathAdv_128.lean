import Mathlib

open scoped InnerProductSpace
open Metric

/-!
# Weakly convergent sequences in a Hilbert space are norm bounded

Let `H` be a (separable) complex Hilbert space and let `u : ℕ → H` be a sequence such that
`fun n => ⟪u n, v⟫` is Cauchy in `ℂ` for every `v ∈ H`.  Then `‖u n‖` is a bounded sequence.

The proof is an application of the **uniform boundedness principle** (Banach–Steinhaus):
each `u n` defines a continuous linear functional `innerSL ℂ (u n) : H →L[ℂ] ℂ`, `v ↦ ⟪u n, v⟫`,
whose operator norm equals `‖u n‖`.  A Cauchy sequence in `ℂ` is bounded, so the family of
functionals is pointwise bounded, and Banach–Steinhaus yields a uniform bound on the operator
norms.

(Separability of `H` is part of the statement as given, but is not needed for the argument.)
-/

theorem melrose_sp2009_8
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H)
    (hconverge : ∀ v : H, CauchySeq (fun n : ℕ => (⟪u n, v⟫_ℂ : ℂ))) :
    ∃ C : ℝ, ∀ n : ℕ, ‖u n‖ ≤ C := by
  -- Pointwise boundedness of the family of functionals `v ↦ ⟪u n, v⟫`.
  have key : ∀ v : H, ∃ C : ℝ, ∀ n : ℕ, ‖(innerSL ℂ (u n)) v‖ ≤ C := by
    intro v
    obtain ⟨C, hC⟩ := (hconverge v).isBounded_range.subset_closedBall 0
    exact ⟨C, fun n => by simpa [mem_closedBall_zero_iff] using hC ⟨n, rfl⟩⟩
  -- Uniform boundedness principle.
  obtain ⟨C, hC⟩ := banach_steinhaus key
  -- `‖innerSL ℂ x‖ = ‖x‖`.
  exact ⟨C, fun n => by simpa [innerSL_apply_norm] using hC n⟩
