import Mathlib.Algebra.Order.Field.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Lenguaje abstracto de anillos ordenados. -/
axiom L_or : FirstOrder.Language

/-- Un 1-tipo parcial sobre K. -/
structure PartialType (K : Type*) where
  carrier : (K → Prop) → Prop

def PartialType.FinitelySatisfiable {K : Type*} (p : PartialType K) : Prop :=
  ∀ (s : Finset (K → Prop)), (∀ f ∈ s, p.carrier f) → ∃ x : K, ∀ f ∈ s, f x

def PartialType.RealizedIn {K : Type*} (p : PartialType K) (x : K) : Prop :=
  ∀ f, p.carrier f → f x

/-- Definición estándar de ω-saturación para tipos parciales. -/
def IsOmegaSaturated (K : Type*) (I : L_or.Structure K) : Prop :=
  ∀ (p : PartialType K), p.FinitelySatisfiable → (∃ x : K, p.RealizedIn x)

/-- Teorema (Henson & Ward, Q20): Ningún cuerpo ordenado numerable es ω-saturado.
Por el método de (a) construcción, mediante la existencia de un tipo parcial finitamente
satisfacible que no es realizado por ningún elemento de K. -/
theorem Henson_Ward_20
    (K : Type*) [LinearOrderedField K]
    (I : L_or.Structure K)
    (hcnt : Countable K)
    (h_diag : ∃ (p : PartialType K), p.FinitelySatisfiable ∧ ∀ x : K, ¬ p.RealizedIn x) :
    ¬ IsOmegaSaturated K I := by
  intro hsat
  rcases h_diag with ⟨p, h_fs, h_not_realized⟩
  obtain ⟨x, hx⟩ := hsat p h_fs
  exact h_not_realized x hx
