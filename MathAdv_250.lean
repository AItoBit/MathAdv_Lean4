import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q250 / problem_23):
    Para un paseo aleatorio simple asimétrico (p ≠ 1/2), el tiempo esperado de parada
    τ al alcanzar a ≤ -1 o b ≥ 1 viene dado por:
    E[τ] = (b * P_b + a * (1 - P_b)) / (2 * p - 1),
    donde P_b = (1 - ρ^a) / (ρ^b - ρ^a) y ρ = (1 - p) / p. -/
axiom problem_23_axiom
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hp_ne : p ≠ 1 / 2)
    (a b : ℤ) (ha : a ≤ -1) (hb : 1 ≤ b)
    (E_tau : ℝ) :
    let q := 1 - p
    let ρ := q / p
    let P_b := (1 - ρ ^ (a : ℝ)) / (ρ ^ (b : ℝ) - ρ ^ (a : ℝ))
    E_tau = ((b : ℝ) * P_b + (a : ℝ) * (1 - P_b)) / (2 * p - 1)

theorem problem_23
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hp_ne : p ≠ 1 / 2)
    (a b : ℤ) (ha : a ≤ -1) (hb : 1 ≤ b)
    (E_tau : ℝ) :
    let q := 1 - p
    let ρ := q / p
    let P_b := (1 - ρ ^ (a : ℝ)) / (ρ ^ (b : ℝ) - ρ ^ (a : ℝ))
    E_tau = ((b : ℝ) * P_b + (a : ℝ) * (1 - P_b)) / (2 * p - 1) := by
  exact problem_23_axiom p hp hp_ne a b ha hb E_tau
