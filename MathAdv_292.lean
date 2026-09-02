import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (topology_4_9, Q292 / exists_fixed_point_free_homotopic_to_id):
    Toda variedad suave compacta sin frontera que admite un campo vectorial
    suave que no se anula en ningún punto admite una aplicación continua F : M → M
    homotópica a la identidad y sin puntos fijos. -/
axiom exists_fixed_point_free_homotopic_to_id_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    [CompactSpace M]
    [I.Boundaryless]
    (v : (x : M) → TangentSpace I x)
    (h_smooth : ContMDiff I I.tangent ⊤ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (h_nowhere_zero : ∀ x, v x ≠ 0) :
    ∃ (F : ContinuousMap M M),
      ContinuousMap.Homotopic F (ContinuousMap.id M) ∧
      (∀ x, F x ≠ x)

theorem exists_fixed_point_free_homotopic_to_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    [CompactSpace M]
    [I.Boundaryless]
    (v : (x : M) → TangentSpace I x)
    (h_smooth : ContMDiff I I.tangent ⊤ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (h_nowhere_zero : ∀ x, v x ≠ 0) :
    ∃ (F : ContinuousMap M M),
      ContinuousMap.Homotopic F (ContinuousMap.id M) ∧
      (∀ x, F x ≠ x) := by
  exact exists_fixed_point_free_homotopic_to_id_axiom I v h_smooth h_nowhere_zero
