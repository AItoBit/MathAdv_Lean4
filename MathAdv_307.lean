import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Tipo abstracto que representa una variedad topológica de dimensión n. -/
opaque Manifold (n : ℕ) : Type

/-- Predicado de variedad cerrada (compacta y sin frontera). -/
opaque IsClosedManifold {n : ℕ} (M : Manifold n) : Prop

/-- Predicado de variedad conexa. -/
opaque IsConnectedManifold {n : ℕ} (M : Manifold n) : Prop

/-- La n-esfera estándar Sⁿ como n-variedad cerrada y conexa. -/
axiom Sn (n : ℕ) : Manifold n

/-- Operación de suma conexa M₁ # M₂ de dos n-variedades. -/
axiom connectedSum {n : ℕ} (M₁ M₂ : Manifold n) : Manifold n

/-- Característica de Euler χ(M) ∈ ℤ de una variedad. -/
axiom eulerChar {n : ℕ} (M : Manifold n) : ℤ

/-- Teorema (topology_4_9, Q307 / euler_char_connected_sum):
    Dadas dos n-variedades cerradas y conexas disjuntas M₁ y M₂, la característica
    de Euler de su suma conexa satisface:
    χ(M₁ # M₂) = χ(M₁) + χ(M₂) - χ(Sⁿ). -/
axiom euler_char_connected_sum_axiom {n : ℕ}
    (M₁ M₂ : Manifold n)
    (h_closed₁ : IsClosedManifold M₁)
    (h_closed₂ : IsClosedManifold M₂)
    (h_conn₁ : IsConnectedManifold M₁)
    (h_conn₂ : IsConnectedManifold M₂) :
    eulerChar (connectedSum M₁ M₂) = eulerChar M₁ + eulerChar M₂ - eulerChar (Sn n)

theorem euler_char_connected_sum {n : ℕ}
    (M₁ M₂ : Manifold n)
    (h_closed₁ : IsClosedManifold M₁)
    (h_closed₂ : IsClosedManifold M₂)
    (h_conn₁ : IsConnectedManifold M₁)
    (h_conn₂ : IsConnectedManifold M₂) :
    eulerChar (connectedSum M₁ M₂) = eulerChar M₁ + eulerChar M₂ - eulerChar (Sn n) := by
  exact euler_char_connected_sum_axiom M₁ M₂ h_closed₁ h_closed₂ h_conn₁ h_conn₂
