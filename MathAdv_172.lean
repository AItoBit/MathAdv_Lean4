import Mathlib

/-!
# An orthogonal basis for a bilinear form on `ℝ²`

The bilinear form `⟨x,y⟩ = x₁y₁ + x₁y₂ + x₂y₁ + 5x₂y₂` on `ℝ²`.
We show that `w₁ = [1,0]ᵀ`, `w₂ = [-1,1]ᵀ` are orthogonal (and anisotropic) for it,
and that they span the same subspace as the standard basis, i.e. they form a basis
obtained from the standard basis by Gram–Schmidt.
-/

abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The bilinear form `⟨x,y⟩ = x₁y₁ + x₁y₂ + x₂y₁ + 5x₂y₂` on `ℝ²`. -/
def B (x y : R2) : ℝ :=
  x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + 5 * x 1 * y 1

theorem question_2 :
  (B (!₂[1, 0] : R2) (!₂[-1, 1] : R2) = 0
   ∧ B (!₂[1, 0] : R2) (!₂[1, 0] : R2) ≠ 0
   ∧ B (!₂[-1, 1] : R2) (!₂[-1, 1] : R2) ≠ 0)
  ∧
    Submodule.span ℝ
      (Set.range ( ![ (!₂[1, 0] : R2), (!₂[0, 1] : R2) ] : Fin 2 → R2 ))
    =
    Submodule.span ℝ
      (Set.range ( ![ (!₂[1, 0] : R2), (!₂[-1, 1] : R2) ] : Fin 2 → R2 )) := by
  have hrange : ∀ a b : R2, Set.range (![a, b] : Fin 2 → R2) = {a, b} := by
    intro a b
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  refine ⟨⟨by norm_num [B], by norm_num [B], by norm_num [B]⟩, ?_⟩
  rw [hrange, hrange]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨1, 1, ?_⟩
      ext i
      fin_cases i <;> simp
  · rw [Submodule.span_le]
    rintro x hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨-1, 1, ?_⟩
      ext i
      fin_cases i <;> simp

-- Sanity check: the proof uses no extra axioms.
#print axioms question_2
