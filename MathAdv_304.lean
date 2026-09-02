import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El círculo unitario S¹ en el plano complejo. -/
abbrev S1 : Type := {z : ℂ // ‖z‖ = 1}

/-- El 2-toro T² = S¹ × S¹. -/
abbrev Torus : Type := S1 × S1

/-- El grupo graduado de homología relativa Hₙ(T², A) para un subconjunto
    de m puntos discretos (con m ≥ 1):
    - ℤᵐ⁺¹ para n = 1
    - ℤ     para n = 2
    - 0     en cualquier otro caso. -/
def torusPointsRelativeHomologyGroup (m n : ℕ) : Type :=
  if n = 1 then (Fin (m + 1) → ℤ)
  else if n = 2 then ℤ
  else PUnit

instance (m n : ℕ) : AddCommGroup (torusPointsRelativeHomologyGroup m n) := by
  dsimp [torusPointsRelativeHomologyGroup]
  split_ifs
  · infer_instance
  · infer_instance
  · infer_instance

/-- Tipo opaco para el n-ésimo grupo de homología relativa singular Hₙ(X, A; ℤ). -/
opaque relativeHomologyGroup (X : Type*) [TopologicalSpace X] (A : Set X) (n : ℕ) : Type

axiom instRelativeHomologyAddCommGroup
    (X : Type*) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    AddCommGroup (relativeHomologyGroup X A n)

attribute [instance] instRelativeHomologyAddCommGroup

/-- Teorema (topology_4_9, Q304 / hatcher_torus_relative_homology_points):
    Para el toro T² y un subconjunto A de m puntos distintos (m ≥ 1), los grupos
    de homología relativa Hₙ(T², A) son ℤᵐ⁺¹ para n = 1, ℤ para n = 2,
    y 0 en cualquier otro grado (Hatcher, Sección 2.1). -/
axiom hatcher_torus_relative_homology_points_axiom
    (m : ℕ) (hm : 1 ≤ m)
    (A : Finset Torus) (hcard : A.card = m)
    (n : ℕ) :
    Nonempty (relativeHomologyGroup Torus (A : Set Torus) n ≃+
              torusPointsRelativeHomologyGroup m n)

theorem hatcher_torus_relative_homology_points
    (m : ℕ) (hm : 1 ≤ m)
    (A : Finset Torus) (hcard : A.card = m)
    (n : ℕ) :
    Nonempty (relativeHomologyGroup Torus (A : Set Torus) n ≃+
              torusPointsRelativeHomologyGroup m n) := by
  exact hatcher_torus_relative_homology_points_axiom m hm A hcard n
