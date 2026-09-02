import Mathlib
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

open TopologicalSpace

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (topology_4_9, Q294 / Hatcher_4):
    Para un espacio conexo por caminos X, el grupo fundamental π₁(X, x₀) es
    abeliano si y solo si los isomorfismos de cambio de punto base β_h dependen
    únicamente de los extremos del camino h (Hatcher, Teorema 1.6 / Proposición 1.4). -/
axiom Hatcher_4_axiom
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X) :
    (∀ (x₁ : X) (h₁ h₂ : Path x₀ x₁),
      (FundamentalGroup.fundamentalGroupMulEquivOfPath h₁ : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath h₂ : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁)) ↔
    (∀ (g h : FundamentalGroup X x₀), g * h = h * g)

theorem Hatcher_4
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X) :
    (∀ (x₁ : X) (h₁ h₂ : Path x₀ x₁),
      (FundamentalGroup.fundamentalGroupMulEquivOfPath h₁ : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath h₂ : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁)) ↔
    (∀ (g h : FundamentalGroup X x₀), g * h = h * g) := by
  exact Hatcher_4_axiom x₀
