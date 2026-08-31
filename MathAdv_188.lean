import Mathlib

/-- The rows of the matrix
`A = ![![-2,-2,1,3], ![3,3,0,-1], ![-1,-1,-2,-5], ![2,2,5,5]]`
do not span `ℝ⁴`: every row has equal first two coordinates, so the span is
contained in the proper subspace `{v | v 0 = v 1}`. -/
theorem question_18 :
  Submodule.span ℝ
    (Set.range
      ( ![
          ![-2, -2, 1, 3],
          ![3, 3, 0, -1],
          ![-1, -1, -2, -5],
          ![2, 2, 5, 5]
        ] : Fin 4 → (Fin 4 → ℝ) ))
  ≠ ⊤ := by
  -- the linear functional `v ↦ v 0 - v 1` vanishes on the span
  set f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (0 : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) -
      (LinearMap.proj (1 : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) with hf
  intro htop
  have hsub : Submodule.span ℝ
      (Set.range ( ![
          ![-2, -2, 1, 3],
          ![3, 3, 0, -1],
          ![-1, -1, -2, -5],
          ![2, 2, 5, 5]
        ] : Fin 4 → (Fin 4 → ℝ) )) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hf, LinearMap.sub_apply,
      LinearMap.proj_apply]
    fin_cases i <;> norm_num
  rw [htop, top_le_iff] at hsub
  have : f (fun j => if j = 0 then (1 : ℝ) else 0) = 0 := by
    rw [← LinearMap.mem_ker, hsub]; trivial
  simp [hf] at this
