import Mathlib

/-- Teorema (number_theory_4_9, Q226 / question_9):
    Todo número natural positivo se puede expresar como suma de cuatro cuadrados
    (Teorema de los cuatro cuadrados de Lagrange, demostrable vía el Lema de Minkowski). -/
theorem question_9 (n : ℕ) (_hn : 0 < n) :
    ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n := by
  exact Nat.sum_four_squares n
