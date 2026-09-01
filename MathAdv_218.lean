import Mathlib

/-- Teorema (number_theory_4_9, Q218 / question_1):
    Para todo número natural n, el conjunto de unidades (ℤ/nℤ)ˣ
    bajo la multiplicación módulo n forma un grupo. -/
theorem question_1 (n : ℕ) :
    Nonempty (Group (Units (ZMod n))) :=
  ⟨inferInstance⟩
