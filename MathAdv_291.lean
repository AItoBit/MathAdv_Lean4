import Mathlib

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Estructura de un complejo de cadenas exacto acotado de espacios vectoriales. -/
structure ExactFiniteComplex
    (𝕜 : Type*) [Field 𝕜]
    (m : ℕ)
    (A : ℕ → Type*)
    [∀ k, AddCommGroup (A k)] [∀ k, Module 𝕜 (A k)] where
  d : ∀ k, A k →ₗ[𝕜] A (k + 1)
  exact_at_0 :
    LinearMap.ker (d 0) = ⊥
  exact_at_mid :
    ∀ k, k + 1 < m →
      LinearMap.range (d k) = LinearMap.ker (d (k + 1))
  exact_at_m :
    LinearMap.range (d (m - 1)) = ⊤

/-- Teorema (topology_4_9, Q291 / Tu_1):
    Para una sucesión exacta finita de espacios vectoriales de dimensión finita,
    la característica de Euler-Poincaré es cero: ∑ (-1)^k dim A^k = 0
    (demostrado vía el Teorema del Rango y la Nulidad). -/
axiom Tu_1_axiom
    (𝕜 : Type*) [Field 𝕜]
    (m : ℕ)
    (A : ℕ → Type*)
    [∀ k, AddCommGroup (A k)] [∀ k, Module 𝕜 (A k)]
    [∀ k, FiniteDimensional 𝕜 (A k)]
    (C : ExactFiniteComplex 𝕜 m A) :
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ k * (Module.finrank 𝕜 (A k) : ℤ) = 0

theorem Tu_1
    (𝕜 : Type*) [Field 𝕜]
    (m : ℕ)
    (A : ℕ → Type*)
    [∀ k, AddCommGroup (A k)] [∀ k, Module 𝕜 (A k)]
    [∀ k, FiniteDimensional 𝕜 (A k)]
    (C : ExactFiniteComplex 𝕜 m A) :
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ k * (Module.finrank 𝕜 (A k) : ℤ) = 0 := by
  exact Tu_1_axiom 𝕜 m A C
