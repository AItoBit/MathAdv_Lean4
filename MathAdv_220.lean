import Mathlib

/-- Teorema (number_theory_4_9, Q220 / question_3):
    Los dos últimos dígitos de 3⁴⁵ son 43, es decir, 3⁴⁵ ≡ 43 (mod 100). -/
theorem question_3 :
    3^45 % 100 = 43 := by
  decide
