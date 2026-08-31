import Mathlib

/-- `Rn n` is the Euclidean space `ℝⁿ` with its standard inner product. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- For any subspace `S ⊆ ℝⁿ`, we have `S ∩ Sᗮ = {0}`. -/
theorem question_17
  {n : ℕ} (S : Submodule ℝ (Rn n)) :
  S ⊓ Sᗮ = ⊥ := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hx, hx'⟩
    exact inner_self_eq_zero (𝕜 := ℝ) |>.mp (hx' x hx)
  · rintro rfl
    exact ⟨S.zero_mem, Sᗮ.zero_mem⟩
