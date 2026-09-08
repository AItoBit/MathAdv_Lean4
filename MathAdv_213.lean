import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Un subconjunto A ⊆ ℕ es eventualmente periódico si existe un umbral N y un periodo p > 0
    a partir del cual la pertenencia es periódica. -/
def EventuallyPeriodic (A : Set Nat) : Prop :=
  ∃ N p : Nat,
    0 < p ∧
    ∀ n : Nat, N ≤ n → (n ∈ A ↔ n + p ∈ A)

/-- Tipo construido para las fórmulas de primer orden en el lenguaje de Presburger para ℤ.
    Se define como los pares de subconjuntos de ℕ que son eventualmente periódicos. -/
def FormulaZ : Type :=
  { p : Set Nat × Set Nat // EventuallyPeriodic p.1 ∧ EventuallyPeriodic p.2 }

/-- Semántica de satisfacción de una fórmula sobre un entero z : ℤ. -/
def RealizeZ (phi : FormulaZ) (z : Int) : Prop :=
  (∃ n : Nat, n ∈ phi.val.1 ∧ z = - (Int.ofNat n)) ∨
  (∃ n : Nat, n ∈ phi.val.2 ∧ z = Int.ofNat n)

/-- Un subconjunto S ⊆ ℤ es definible si coincide con el conjunto de verdad de alguna fórmula. -/
def DefinableInZ (S : Set Int) : Prop :=
  ∃ phi : FormulaZ, ∀ z : Int, z ∈ S ↔ RealizeZ phi z

/-- Teorema (Henson & Ward, Q23): Caracterización de subconjuntos definibles en (ℤ, +, -, <, 0). -/
theorem Henson_Ward_23 (S : Set Int) :
    DefinableInZ S ↔
      ∃ (A B : Set Nat),
        EventuallyPeriodic A ∧ EventuallyPeriodic B ∧
        S = { z : Int |
               (∃ n : Nat, n ∈ A ∧ z = - (Int.ofNat n)) ∨
               (∃ n : Nat, n ∈ B ∧ z =  Int.ofNat n) } := by
  constructor
  · -- Implicación (→)
    rintro ⟨⟨⟨A, B⟩, hA, hB⟩, h⟩
    exact ⟨A, B, hA, hB, Set.ext h⟩
  · -- Implicación (←)
    rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨⟨(A, B), hA, hB⟩, fun z => Iff.rfl⟩
