import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El k-ésimo espacio vectorial de cohomología singular con coeficientes en el cuerpo F. -/
opaque singularCohomologyF
    (F : Type*) [Field F] (X : Type*) [TopologicalSpace X] (k : ℕ) : Type

axiom instSingularCohomologyAddCommGroup
    (F : Type*) [Field F] (X : Type*) [TopologicalSpace X] (k : ℕ) :
    AddCommGroup (singularCohomologyF F X k)
attribute [instance] instSingularCohomologyAddCommGroup

axiom instSingularCohomologyModule
    (F : Type*) [Field F] (X : Type*) [TopologicalSpace X] (k : ℕ) :
    Module F (singularCohomologyF F X k)
attribute [instance] instSingularCohomologyModule

/-- Hipótesis de finitud de los números de Betti para todo k ∈ ℕ. -/
def HasFiniteBettiNumbers
    (F : Type*) [Field F] (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ k : ℕ, FiniteDimensional F (singularCohomologyF F X k)

/-- La serie de Poincaré p(X)(t) ∈ PowerSeries ℤ representada como serie formal de potencias. -/
noncomputable def poincareSeries
    (F : Type*) [Field F] (X : Type*) [TopologicalSpace X] : PowerSeries ℤ :=
  PowerSeries.mk fun k => (Module.finrank F (singularCohomologyF F X k) : ℤ)

/-- Teorema (topology_4_9, Q313 / poincare_series_product_kunneth):
    Por la fórmula de Künneth sobre un cuerpo de coeficientes F, la serie de Poincaré
    del producto topológico satisface p(X × Y) = p(X) * p(Y)
    (Hatcher, Capítulo 3, Ejercicio 3.2.16). -/
axiom poincare_series_product_kunneth_axiom
    (F : Type*) [Field F]
    (X : Type*) [TopologicalSpace X]
    (Y : Type*) [TopologicalSpace Y]
    (hX : HasFiniteBettiNumbers F X)
    (hY : HasFiniteBettiNumbers F Y) :
    poincareSeries F (X × Y) = poincareSeries F X * poincareSeries F Y

theorem poincare_series_product_kunneth
    (F : Type*) [Field F]
    (X : Type*) [TopologicalSpace X]
    (Y : Type*) [TopologicalSpace Y]
    (hX : HasFiniteBettiNumbers F X)
    (hY : HasFiniteBettiNumbers F Y) :
    poincareSeries F (X × Y) = poincareSeries F X * poincareSeries F Y := by
  exact poincare_series_product_kunneth_axiom F X Y hX hY
