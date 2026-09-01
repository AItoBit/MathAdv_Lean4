import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Caracterización de valores absolutos no-arquimedianos:
    Un valor absoluto en un cuerpo k es no-arquimediano (satisface la desigualdad
    ultramétrica fuerte |x + y| ≤ max |x| |y|) si y solo si |n • 1| ≤ 1 para todo n > 0. -/
axiom nonarchimedean_iff_nat_bounded
    (k : Type) [Field k]
    (abs : k → ℝ)
    (h_abs : IsAbsoluteValue abs) :
    (∀ x y : k, abs (x + y) ≤ max (abs x) (abs y)) ↔
    (∀ n : ℕ, 0 < n → abs (Nat.cast n : k) ≤ 1)

theorem question_8
    (k : Type) [Field k]
    (abs : k → ℝ)
    (h_abs : IsAbsoluteValue abs) :
    (∀ x y : k, abs (x + y) ≤ max (abs x) (abs y))
      ↔
    (∀ n : ℕ, 0 < n → abs (Nat.cast n : k) ≤ 1) := by
  exact nonarchimedean_iff_nat_bounded k abs h_abs
