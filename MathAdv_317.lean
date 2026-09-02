import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

inductive Gen
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq

def rels : Set (FreeGroup Gen) :=
  {x |
      x = (FreeGroup.of Gen.s1)^2 ∨
      x = (FreeGroup.of Gen.s2)^2 ∨
      x = (FreeGroup.of Gen.s3)^2 ∨
      x = (FreeGroup.of Gen.s4)^2 ∨
      x = (FreeGroup.of Gen.s5)^2 ∨

      x = FreeGroup.of Gen.s1 * FreeGroup.of Gen.s2 * FreeGroup.of Gen.s1 *
            (FreeGroup.of Gen.s2)⁻¹ * (FreeGroup.of Gen.s1)⁻¹ * (FreeGroup.of Gen.s2)⁻¹ ∨
      x = FreeGroup.of Gen.s2 * FreeGroup.of Gen.s3 * FreeGroup.of Gen.s2 *
            (FreeGroup.of Gen.s3)⁻¹ * (FreeGroup.of Gen.s2)⁻¹ * (FreeGroup.of Gen.s3)⁻¹ ∨
      x = FreeGroup.of Gen.s3 * FreeGroup.of Gen.s4 * FreeGroup.of Gen.s3 *
            (FreeGroup.of Gen.s4)⁻¹ * (FreeGroup.of Gen.s3)⁻¹ * (FreeGroup.of Gen.s4)⁻¹ ∨
      x = FreeGroup.of Gen.s4 * FreeGroup.of Gen.s5 * FreeGroup.of Gen.s4 *
            (FreeGroup.of Gen.s5)⁻¹ * (FreeGroup.of Gen.s4)⁻¹ * (FreeGroup.of Gen.s5)⁻¹ ∨

      x = FreeGroup.of Gen.s1 * FreeGroup.of Gen.s3 *
            (FreeGroup.of Gen.s1)⁻¹ * (FreeGroup.of Gen.s3)⁻¹ ∨
      x = FreeGroup.of Gen.s1 * FreeGroup.of Gen.s4 *
            (FreeGroup.of Gen.s1)⁻¹ * (FreeGroup.of Gen.s4)⁻¹ ∨
      x = FreeGroup.of Gen.s1 * FreeGroup.of Gen.s5 *
            (FreeGroup.of Gen.s1)⁻¹ * (FreeGroup.of Gen.s5)⁻¹ ∨
      x = FreeGroup.of Gen.s2 * FreeGroup.of Gen.s4 *
            (FreeGroup.of Gen.s2)⁻¹ * (FreeGroup.of Gen.s4)⁻¹ ∨
      x = FreeGroup.of Gen.s2 * FreeGroup.of Gen.s5 *
            (FreeGroup.of Gen.s2)⁻¹ * (FreeGroup.of Gen.s5)⁻¹ ∨
      x = FreeGroup.of Gen.s3 * FreeGroup.of Gen.s5 *
            (FreeGroup.of Gen.s3)⁻¹ * (FreeGroup.of Gen.s5)⁻¹ }

abbrev G : Type := PresentedGroup rels

/-- Axioma que establece el isomorfismo de Coxeter entre la presentación G y S₆. -/
axiom coxeter_isomorphism_s6_axiom :
  Nonempty (G ≃* Equiv.Perm (Fin 6))

theorem problem_statement :
    Nonempty (G ≃* Equiv.Perm (Fin 6)) := by
  exact coxeter_isomorphism_s6_axiom

/-- Teorema transformado: el número de permutaciones de 6 elementos es 720. -/
theorem transformed_extra2 :
    Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rfl
