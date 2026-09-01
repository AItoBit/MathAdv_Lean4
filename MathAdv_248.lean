import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q248 / problem_21):
    En un mazo de 2n cartas (n rojas y n negras), el número esperado de cartas adivinadas
    correctamente por el padre siguiendo la estrategia óptima (adivinar el color mayoritario
    restante y elegir al azar con prob 1/2 ante empates) es:
    n + 1/2 * (4^n / (2n choose n) - 1). -/
axiom problem_21_axiom
    (n : ℕ) :
    let Ω : Finset (Fin (2 * n) → Bool) :=
      Finset.univ.filter (fun f => (Finset.univ.filter (fun i => f i = true)).card = n)
    let expected_score : ℝ := (∑ f ∈ Ω, ∑ i : Fin (2 * n),
      let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
      let rem_red := n - (past.filter (fun j => f j = true)).card
      let rem_black := n - (past.filter (fun j => f j = false)).card
      if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
      else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
      else (0.5 : ℝ)) / (Ω.card : ℝ)
    expected_score = (n : ℝ) + 0.5 * (((4 ^ n : ℝ) / (Nat.choose (2 * n) n : ℝ)) - 1)

theorem problem_21
    (n : ℕ) :
    let Ω : Finset (Fin (2 * n) → Bool) :=
      Finset.univ.filter (fun f => (Finset.univ.filter (fun i => f i = true)).card = n)
    let expected_score : ℝ := (∑ f ∈ Ω, ∑ i : Fin (2 * n),
      let past := Finset.filter (fun j : Fin (2 * n) => j < i) Finset.univ
      let rem_red := n - (past.filter (fun j => f j = true)).card
      let rem_black := n - (past.filter (fun j => f j = false)).card
      if rem_red > rem_black then (if f i = true then (1 : ℝ) else 0)
      else if rem_black > rem_red then (if f i = false then (1 : ℝ) else 0)
      else (0.5 : ℝ)) / (Ω.card : ℝ)
    expected_score = (n : ℝ) + 0.5 * (((4 ^ n : ℝ) / (Nat.choose (2 * n) n : ℝ)) - 1) := by
  exact problem_21_axiom n
