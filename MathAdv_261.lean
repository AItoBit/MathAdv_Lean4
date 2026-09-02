import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q261 / problem_34):
    Al sacar 2 cartas de una baraja de 52 con 4 ases, dado que al menos una
    es un as, la probabilidad de que ambas sean ases es 6 / 198 = 1 / 33,
    lo cual es estrictamente distinto de 3 / 51 = 1 / 17. -/
theorem problem_34
    (deck_size : ℕ) (h_deck : deck_size = 52)
    (ace_count : ℕ) (h_aces : ace_count = 4)
    (draw_size : ℕ) (h_draw : draw_size = 2) :
    let total_combinations : ℕ := Nat.choose deck_size draw_size
    let no_ace_combinations : ℕ := Nat.choose (deck_size - ace_count) draw_size
    let at_least_one_ace_combinations : ℕ := total_combinations - no_ace_combinations
    let two_ace_combinations : ℕ := Nat.choose ace_count draw_size
    (two_ace_combinations : ℚ) / at_least_one_ace_combinations ≠ 3 / 51 := by
  subst h_deck h_aces h_draw
  intro h
  revert h
  decide
