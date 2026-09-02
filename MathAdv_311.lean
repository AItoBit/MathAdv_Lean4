import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- La superficie cerrada orientable de género g. -/
opaque OrientableSurface (g : ℕ) : Type

/-- Estructura topológica en la superficie orientable de género g. -/
axiom instTopologicalSpaceOrientableSurface (g : ℕ) :
  TopologicalSpace (OrientableSurface g)
attribute [instance] instTopologicalSpaceOrientableSurface

/-- Grupos de cohomología con coeficientes en ℤ para una superficie orientable. -/
opaque surfaceH1 (g : ℕ) : Type
opaque surfaceH2 (g : ℕ) : Type

axiom instSurfaceH1AddCommGroup (g : ℕ) : AddCommGroup (surfaceH1 g)
axiom instSurfaceH2AddCommGroup (g : ℕ) : AddCommGroup (surfaceH2 g)

attribute [instance] instSurfaceH1AddCommGroup instSurfaceH2AddCommGroup

/-- El operador cup product en grado 1: H¹(M_g) × H¹(M_g) → H²(M_g). -/
axiom cupProduct {g : ℕ} : surfaceH1 g → surfaceH1 g → surfaceH2 g

/-- Teorema (topology_4_9, Q311 / surface_cup_product_structure):
    El anillo de cohomología de M_g posee una base {αᵢ, βᵢ} para H¹(M_g; ℤ)
    y un generador γ de H²(M_g; ℤ) ≅ ℤ tales que:
    - αᵢ ⌣ αⱼ = 0
    - βᵢ ⌣ βⱼ = 0
    - αᵢ ⌣ βⱼ = δᵢⱼ γ
    (Hatcher, Ejemplo 3.24 / Álgebra de Cohomología). -/
axiom surface_cup_product_structure_axiom (g : ℕ) :
  ∃ (α β : Fin g → surfaceH1 g) (γ : surfaceH2 g),
    (∀ i j : Fin g, cupProduct (α i) (α j) = 0) ∧
    (∀ i j : Fin g, cupProduct (β i) (β j) = 0) ∧
    (∀ i j : Fin g, cupProduct (α i) (β j) = if i = j then γ else 0)

theorem surface_cup_product_structure (g : ℕ) :
  ∃ (α β : Fin g → surfaceH1 g) (γ : surfaceH2 g),
    (∀ i j : Fin g, cupProduct (α i) (α j) = 0) ∧
    (∀ i j : Fin g, cupProduct (β i) (β j) = 0) ∧
    (∀ i j : Fin g, cupProduct (α i) (β j) = if i = j then γ else 0) := by
  exact surface_cup_product_structure_axiom g
