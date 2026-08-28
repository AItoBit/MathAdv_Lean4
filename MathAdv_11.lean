import Mathlib

/--
**Problema (Gallian 12):**
El grupo aditivo de los números racionales $(\mathbb{Q}, +)$ no posee
ningún subgrupo propio de índice finito.
-/
theorem Gallian_12 :
    ¬ ∃ H : AddSubgroup ℚ, H.FiniteIndex ∧ H ≠ ⊤ := by
  sorry
