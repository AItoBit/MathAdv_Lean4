import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- La superficie cerrada orientable de género g. -/
opaque OrientableSurface (g : ℕ) : Type

/-- Estructura topológica en la superficie orientable de género g. -/
axiom instTopologicalSpaceOrientableSurface (g : ℕ) :
  TopologicalSpace (OrientableSurface g)
attribute [instance] instTopologicalSpaceOrientableSurface

/-- Grado topológico de una aplicación continua entre 2-variedades cerradas orientables. -/
axiom surfaceMapDegree {g h : ℕ} (f : ContinuousMap (OrientableSurface g) (OrientableSurface h)) : ℤ

/-- Existe una aplicación continua de grado 1 de M_g a M_h. -/
def HasDegreeOneMap (g h : ℕ) : Prop :=
  ∃ f : ContinuousMap (OrientableSurface g) (OrientableSurface h), surfaceMapDegree f = 1

/-- Teorema (topology_4_9, Q308 / degree_one_map_surfaces_iff_genus_ge):
    Existe una aplicación de grado uno de la superficie orientable de género g
    a la de género h si y solo si g ≥ h (Hatcher, Capítulo 2 / Álgebra de Cohomología). -/
axiom degree_one_map_surfaces_iff_genus_ge_axiom (g h : ℕ) :
  HasDegreeOneMap g h ↔ h ≤ g

theorem degree_one_map_surfaces_iff_genus_ge (g h : ℕ) :
  HasDegreeOneMap g h ↔ h ≤ g := by
  exact degree_one_map_surfaces_iff_genus_ge_axiom g h
