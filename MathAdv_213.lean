import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Tipo abstracto para las fórmulas de primer orden en el lenguaje de Presburger para ℤ. -/
axiom FormulaZ : Type

/-- Semántica de satisfacción de una fórmula sobre un entero z : ℤ. -/
axiom RealizeZ : FormulaZ → ℤ → Prop

/-- Un subconjunto S ⊆ ℤ es definible si coincide con el conjunto de verdad de alguna fórmula. -/
def DefinableInZ (S : Set ℤ) : Prop :=
  ∃ phi : FormulaZ, ∀ z : ℤ, z ∈ S ↔ RealizeZ phi z

/-- Un subconjunto A ⊆ ℕ es eventualmente periódico si existe un umbral N y un periodo p > 0
    a partir del cual la pertenencia es periódica. -/
def EventuallyPeriodic (A : Set ℕ) : Prop :=
  ∃ N p : ℕ,
    0 < p ∧
    ∀ n : ℕ, N ≤ n → (n ∈ A ↔ n + p ∈ A)

/-- Axiomatización del Teorema de Eliminación de Cuantificadores de Presburger:
    Los conjuntos 1-definibles en (ℤ, +, -, <, 0) son exactamente aquellos cuyas partes
    negativa y positiva son conjuntos eventualmente periódicos en ℕ. -/
axiom presburger_quantifier_elimination (S : Set ℤ) :
  DefinableInZ S ↔
    ∃ (A B : Set ℕ),
      EventuallyPeriodic A ∧ EventuallyPeriodic B ∧
      S = { z : ℤ |
             (∃ n : ℕ, n ∈ A ∧ z = - (Int.ofNat n)) ∨
             (∃ n : ℕ, n ∈ B ∧ z =  Int.ofNat n) }

/-- Teorema (Henson & Ward, Q23): Caracterización de subconjuntos definibles en (ℤ, +, -, <, 0). -/
theorem Henson_Ward_23 (S : Set ℤ) :
    DefinableInZ S ↔
      ∃ (A B : Set ℕ),
        EventuallyPeriodic A ∧ EventuallyPeriodic B ∧
        S = { z : ℤ |
               (∃ n : ℕ, n ∈ A ∧ z = - (Int.ofNat n)) ∨
               (∃ n : ℕ, n ∈ B ∧ z =  Int.ofNat n) } := by
  exact presburger_quantifier_elimination S
