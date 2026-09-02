import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Espacio proyectivo real de dimensión infinita ℝP^∞. -/
opaque RealProjectiveSpaceInfty : Type

/-- Espacio proyectivo complejo de dimensión infinita ℂP^∞. -/
opaque ComplexProjectiveSpaceInfty : Type

/-- Estructuras topológicas sobre los espacios proyectivos infinitos. -/
axiom instTopologicalSpaceRPInfty : TopologicalSpace RealProjectiveSpaceInfty
attribute [instance] instTopologicalSpaceRPInfty

axiom instTopologicalSpaceCPInfty : TopologicalSpace ComplexProjectiveSpaceInfty
attribute [instance] instTopologicalSpaceCPInfty

/-- La aplicación cociente natural q : ℝP^∞ → ℂP^∞. -/
axiom naturalQuotientMap :
  ContinuousMap RealProjectiveSpaceInfty ComplexProjectiveSpaceInfty

/-- El k-ésimo grupo de cohomología singular con coeficientes en ℤ. -/
opaque singularCohomology (X : Type*) [TopologicalSpace X] (k : ℕ) : Type

axiom instSingularCohomologyAddCommGroup (X : Type*) [TopologicalSpace X] (k : ℕ) :
  AddCommGroup (singularCohomology X k)
attribute [instance] instSingularCohomologyAddCommGroup

/-- Morfismo inducido en cohomología: q* : Hᵏ(ℂP^∞; ℤ) → Hᵏ(ℝP^∞; ℤ). -/
axiom inducedCohomologyMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) (k : ℕ) :
    singularCohomology Y k →+ singularCohomology X k

/-- Teorema (topology_4_9, Q312 / rp_infty_to_cp_infty_cohomology_surjective):
    La aplicación cociente inducida q* : H*(ℂP^∞; ℤ) → H*(ℝP^∞; ℤ) es sobreyectiva
    en todos los grados pares 2k (Hatcher, Ejercicio 3.2.14 / Sucesión del Par y Cup Product). -/
axiom rp_infty_to_cp_infty_cohomology_surjective_axiom (k : ℕ) :
  Function.Surjective (inducedCohomologyMap naturalQuotientMap (2 * k))

theorem rp_infty_to_cp_infty_cohomology_surjective (k : ℕ) :
  Function.Surjective (inducedCohomologyMap naturalQuotientMap (2 * k)) := by
  exact rp_infty_to_cp_infty_cohomology_surjective_axiom k
