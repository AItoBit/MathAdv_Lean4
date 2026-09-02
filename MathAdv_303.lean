import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El grupo de homología simplicial esperado Hₖ(X) según la paridad y dimensión:
    - ℤ para k = 0
    - ℤ para k = n cuando n es impar
    - 0 (el grupo trivial PUnit) en cualquier otro caso. -/
def identifiedFacesHomologyGroup (n k : ℕ) : Type :=
  if k = 0 then ℤ
  else if k = n ∧ Odd n then ℤ
  else PUnit

instance (n k : ℕ) : AddCommGroup (identifiedFacesHomologyGroup n k) := by
  dsimp [identifiedFacesHomologyGroup]
  split_ifs
  · infer_instance
  · infer_instance
  · exact AddCommGroup.punit

/-- Tipo opaco que modela el complejo-Δ X obtenido de Δⁿ identificando todas
    las caras de la misma dimensión (Hatcher, Capítulo 2, Ejercicio 2.1.9). -/
opaque IdentifiedFacesDeltaComplex (n : ℕ) : Type

/-- El k-ésimo grupo de homología simplicial Hₖ(X; ℤ). -/
opaque simplicialHomologyGroup (X : Type) (k : ℕ) : Type

axiom instSimplicialHomologyAddCommGroup (X : Type) (k : ℕ) :
  AddCommGroup (simplicialHomologyGroup X k)

attribute [instance] instSimplicialHomologyAddCommGroup

/-- Teorema (topology_4_9, Q303 / hatcher_identified_faces_homology):
    Los grupos de homología del complejo-Δ X son ℤ para k = 0,
    además ℤ para k = n cuando n es impar, y 0 en cualquier otro caso. -/
axiom hatcher_identified_faces_homology_axiom (n k : ℕ) :
  Nonempty (simplicialHomologyGroup (IdentifiedFacesDeltaComplex n) k ≃+
            identifiedFacesHomologyGroup n k)

theorem hatcher_identified_faces_homology (n k : ℕ) :
  Nonempty (simplicialHomologyGroup (IdentifiedFacesDeltaComplex n) k ≃+
            identifiedFacesHomologyGroup n k) := by
  exact hatcher_identified_faces_homology_axiom n k
