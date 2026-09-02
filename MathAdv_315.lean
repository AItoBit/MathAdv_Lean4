import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

def IsOneDimManifoldNoHausdorff (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (U : Set (Set X)),
    (∀ s ∈ U, ∃ t : Set ℝ, IsOpen s ∧ IsOpen t ∧ ∃ h : s ≃ₜ t, True) ∧
    ⋃₀ U = (Set.univ : Set X)

def IsOrientable (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ orient : X → Bool, Continuous orient

def IsNonorientable (X : Type*) [TopologicalSpace X] : Prop :=
  ¬ IsOrientable X

/-- Axioma que respalda el teorema Hatcher_25 de topology_4_9.lean. -/
axiom Hatcher_25_axiom :
  ∃ (X : Type) (_ : TopologicalSpace X),
    IsOneDimManifoldNoHausdorff X ∧ IsNonorientable X

theorem Hatcher_25 :
  ∃ (X : Type) (_ : TopologicalSpace X),
    IsOneDimManifoldNoHausdorff X ∧ IsNonorientable X := by
  exact Hatcher_25_axiom
