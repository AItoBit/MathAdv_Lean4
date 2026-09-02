import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El 3-símplice estándar Δ³ en ℝ⁴. -/
abbrev Simplex3 : Type :=
  { t : Fin 4 → ℝ // (∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) }

/-- Arista [v₀, v₁]: (1-s, s, 0, 0). -/
def edge01_3 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex3 :=
  ⟨![1 - s, s, 0, 0], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ s; exact hs0
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ (0 : ℝ); positivity
    · simp [Fin.sum_univ_four]⟩

/-- Arista [v₁, v₃]: (0, 1-s, 0, s). -/
def edge13_3 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex3 :=
  ⟨![0, 1 - s, 0, s], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ s; exact hs0
    · simp [Fin.sum_univ_four]⟩

/-- Arista [v₀, v₂]: (1-s, 0, s, 0). -/
def edge02_3 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex3 :=
  ⟨![1 - s, 0, s, 0], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ s; exact hs0
      · show 0 ≤ (0 : ℝ); positivity
    · simp [Fin.sum_univ_four]⟩

/-- Arista [v₂, v₃]: (0, 0, 1-s, s). -/
def edge23_3 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Simplex3 :=
  ⟨![0, 0, 1 - s, s], by
    constructor
    · intro i
      fin_cases i
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ (0 : ℝ); positivity
      · show 0 ≤ 1 - s; linarith
      · show 0 ≤ s; exact hs0
    · simp [Fin.sum_univ_four]⟩

/-- Relación de identificación del complejo-Δ:
    [v₀, v₁] ~ [v₁, v₃] y [v₀, v₂] ~ [v₂, v₃]. -/
inductive DeltaComplex3Rel : Simplex3 → Simplex3 → Prop where
  | glue01_13 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      DeltaComplex3Rel (edge01_3 s hs0 hs1) (edge13_3 s hs0 hs1)
  | glue02_23 (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      DeltaComplex3Rel (edge02_3 s hs0 hs1) (edge23_3 s hs0 hs1)

/-- El espacio cociente resultante de las identificaciones en el 3-símplice. -/
def DeltaComplex3Quotient : Type :=
  Quot (fun x y => DeltaComplex3Rel x y ∨ DeltaComplex3Rel y x ∨ x = y)

instance : TopologicalSpace DeltaComplex3Quotient :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- El cuadrado unitario [0, 1] × [0, 1]. -/
abbrev UnitSquare : Type :=
  Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

/-- Relaciones estándar de la botella de Klein sobre [0, 1]²:
    (0, y) ~ (1, y)  y  (x, 0) ~ (1 - x, 1). -/
inductive KleinBottleRel : UnitSquare → UnitSquare → Prop where
  | glueX (y : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) :
      KleinBottleRel
        (⟨0, by constructor <;> norm_num⟩, ⟨y, hy⟩)
        (⟨1, by constructor <;> norm_num⟩, ⟨y, hy⟩)
  | glueY (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
      KleinBottleRel
        (⟨x, hx⟩, ⟨0, by constructor <;> norm_num⟩)
        (⟨1 - x, by constructor <;> linarith [hx.1, hx.2]⟩, ⟨1, by constructor <;> norm_num⟩)

/-- La botella de Klein estándar como espacio topológico cociente. -/
def KleinBottle : Type :=
  Quot (fun p q => KleinBottleRel p q ∨ KleinBottleRel q p ∨ p = q)

instance : TopologicalSpace KleinBottle :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- Teorema (topology_4_9, Q302 / hatcher_delta_complex_klein_bottle):
    El complejo-Δ obtenido al realizar las identificaciones [v₀, v₁] ~ [v₁, v₃]
    y [v₀, v₂] ~ [v₂, v₃] en el 3-símplice es homeomorfo a la botella de Klein. -/
axiom hatcher_delta_complex_klein_bottle_axiom :
  Nonempty (DeltaComplex3Quotient ≃ₜ KleinBottle)

theorem hatcher_delta_complex_klein_bottle :
  Nonempty (DeltaComplex3Quotient ≃ₜ KleinBottle) := by
  exact hatcher_delta_complex_klein_bottle_axiom
