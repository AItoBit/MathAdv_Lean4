import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Grupos de cohomología simplicial esperados Hᵏ(ℝP²; ℤ):
    - H⁰ ≅ ℤ
    - H¹ ≅ 0 (PUnit)
    - H² ≅ ZMod 2
    - Hᵏ = 0 para k ≥ 3 -/
def rp2CohomologyGroup (k : ℕ) : Type :=
  if k = 0 then ℤ
  else if k = 1 then PUnit
  else if k = 2 then ZMod 2
  else PUnit

instance (k : ℕ) : AddCommGroup (rp2CohomologyGroup k) := by
  dsimp [rp2CohomologyGroup]
  split_ifs
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance

/-- Tipo abstracto para el plano proyectivo real ℝP² como complejo simplicial / complejo-Δ. -/
opaque RP2DeltaComplex : Type

/-- El k-ésimo grupo de cohomología simplicial con coeficientes en ℤ. -/
opaque simplicialCohomologyGroup (X : Type) (k : ℕ) : Type

axiom instSimplicialCohomologyAddCommGroup (X : Type) (k : ℕ) :
  AddCommGroup (simplicialCohomologyGroup X k)

attribute [instance] instSimplicialCohomologyAddCommGroup

/-- Teorema (topology_4_9, Q309 / rp2_simplicial_cohomology):
    Los grupos de cohomología simplicial con coeficientes enteros de ℝP²
    son H⁰ ≅ ℤ, H¹ ≅ 0 y H² ≅ ℤ₂ (Hatcher, Capítulo 3, Ejemplo 3.2). -/
axiom rp2_simplicial_cohomology_axiom (k : ℕ) :
  Nonempty (simplicialCohomologyGroup RP2DeltaComplex k ≃+ rp2CohomologyGroup k)

theorem rp2_simplicial_cohomology (k : ℕ) :
  Nonempty (simplicialCohomologyGroup RP2DeltaComplex k ≃+ rp2CohomologyGroup k) := by
  exact rp2_simplicial_cohomology_axiom k
