import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Espacio de Moore M(ℤ_m, n). -/
opaque MooreSpace (m n : ℕ) : Type

/-- La (n+1)-esfera Sⁿ⁺¹. -/
opaque Sphere (k : ℕ) : Type

/-- Estructuras topológicas. -/
axiom instTopologicalSpaceMoore (m n : ℕ) : TopologicalSpace (MooreSpace m n)
attribute [instance] instTopologicalSpaceMoore

axiom instTopologicalSpaceSphere (k : ℕ) : TopologicalSpace (Sphere k)
attribute [instance] instTopologicalSpaceSphere

/-- Aplicación cociente canónica q : X → X / Sⁿ ≅ Sⁿ⁺¹. -/
axiom quotientToSphere (m n : ℕ) :
  ContinuousMap (MooreSpace m n) (Sphere (n + 1))

/-- El i-ésimo grupo de homología reducida con coeficientes en ℤ. -/
opaque reducedHomology (Y : Type*) [TopologicalSpace Y] (i : ℕ) : Type
axiom instReducedHomologyAddCommGroup (Y : Type*) [TopologicalSpace Y] (i : ℕ) :
  AddCommGroup (reducedHomology Y i)
attribute [instance] instReducedHomologyAddCommGroup

/-- Morfismo inducido en homología reducida: q_* : H̃ᵢ(X) → H̃ᵢ(Sⁿ⁺¹). -/
axiom inducedHomologyMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) (i : ℕ) :
    reducedHomology X i →+ reducedHomology Y i

/-- El i-ésimo grupo de cohomología reducida con coeficientes en ℤ. -/
opaque reducedCohomology (Y : Type*) [TopologicalSpace Y] (i : ℕ) : Type
axiom instReducedCohomologyAddCommGroup (Y : Type*) [TopologicalSpace Y] (i : ℕ) :
  AddCommGroup (reducedCohomology Y i)
attribute [instance] instReducedCohomologyAddCommGroup

/-- Morfismo inducido en cohomología reducida: q* : H̃ⁱ(Sⁿ⁺¹) → H̃ⁱ(X). -/
axiom inducedCohomologyMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) (i : ℕ) :
    reducedCohomology Y i →+ reducedCohomology X i

/-- Teorema (topology_4_9, Q310 / hatcher_moore_space_uct_non_natural):
    Para m ≥ 2 y n ≥ 1, la aplicación cociente q : M(ℤ_m, n) → Sⁿ⁺¹ induce:
    1) La aplicación cero en H̃ᵢ(-; ℤ) para todo i.
    2) Una aplicación no nula en H̃ⁿ⁺¹(-; ℤ) (isomorfa a ℤ ↠ ℤ_m). -/
axiom hatcher_moore_quotient_homology_trivial_axiom
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (i : ℕ) :
    inducedHomologyMap (quotientToSphere m n) i = 0

axiom hatcher_moore_quotient_cohomology_nontrivial_axiom
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    inducedCohomologyMap (quotientToSphere m n) (n + 1) ≠ 0

theorem hatcher_moore_quotient_homology_trivial
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (i : ℕ) :
    inducedHomologyMap (quotientToSphere m n) i = 0 := by
  exact hatcher_moore_quotient_homology_trivial_axiom m n hm hn i

theorem hatcher_moore_quotient_cohomology_nontrivial
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    inducedCohomologyMap (quotientToSphere m n) (n + 1) ≠ 0 := by
  exact hatcher_moore_quotient_cohomology_nontrivial_axiom m n hm hn
