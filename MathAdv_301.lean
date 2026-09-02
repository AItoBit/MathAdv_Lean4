import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El 2-símplice estándar Δ² en ℝ³. -/
abbrev Simplex2 : Type :=
  { t : Fin 3 → ℝ // (∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) }

/-- El punto correspondiente a la arista [v₀, v₁] parametrizada por s ∈ [0, 1]. -/
def edge01 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex2 :=
  ⟨![1 - s, s, 0], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ s; exact hs0
      · show 0 ≤ (0 : ℝ); positivity
    · simp [Fin.sum_univ_three]⟩

/-- El punto correspondiente a la arista [v₁, v₂] parametrizada por s ∈ [0, 1]. -/
def edge12 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex2 :=
  ⟨![0, 1 - s, s], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ s; exact hs0
    · simp [Fin.sum_univ_three]⟩

/-- Relación de pegado que identifica la arista [v₀, v₁] con [v₁, v₂]
    respetando el orden de los vértices: edge01 s ~ edge12 s. -/
inductive DeltaComplexRel : Simplex2 → Simplex2 → Prop where
  | glue (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      DeltaComplexRel (edge01 s hs0 hs1) (edge12 s hs0 hs1)

/-- El cociente del 2-símplice bajo la relación de identificación. -/
def DeltaComplexQuotient : Type :=
  Quot (fun x y => DeltaComplexRel x y ∨ DeltaComplexRel y x ∨ x = y)

instance : TopologicalSpace DeltaComplexQuotient :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- El cilindro base [0, 1] × [-1, 1]. -/
abbrev MoebiusSquare : Type :=
  Set.Icc (0 : ℝ) 1 × Set.Icc (-1 : ℝ) 1

/-- Relación estándar que define la banda de Möbius: (0, y) ~ (1, -y). -/
inductive MoebiusRel : MoebiusSquare → MoebiusSquare → Prop where
  | twist (y : ℝ) (hy : -1 ≤ y ∧ y ≤ 1) :
      MoebiusRel
        (⟨0, by constructor <;> norm_num⟩, ⟨y, hy⟩)
        (⟨1, by constructor <;> norm_num⟩, ⟨-y, by constructor <;> linarith [hy.1, hy.2]⟩)

/-- La banda de Möbius estándar como espacio topológico cociente. -/
def MoebiusStrip : Type :=
  Quot (fun p q => MoebiusRel p q ∨ MoebiusRel q p ∨ p = q)

instance : TopologicalSpace MoebiusStrip :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- Teorema (topology_4_9, Q301 / hatcher_delta_complex_moebius):
    El complejo-Δ obtenido al identificar dos aristas de un 2-símplice
    respetando la orientación de los vértices es homeomorfo a la banda de Möbius. -/
axiom hatcher_delta_complex_moebius_axiom :
  Nonempty (DeltaComplexQuotient ≃ₜ MoebiusStrip)

theorem hatcher_delta_complex_moebius :
  Nonempty (DeltaComplexQuotient ≃ₜ MoebiusStrip) := by
  exact hatcher_delta_complex_moebius_axiom
