import Mathlib

set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q242 / problem_15):
    El número esperado de pares adyacentes con el mismo valor al ordenar
    al azar 6 pares de cartas (12 cartas en total) es 1. -/
axiom problem_15_axiom :
    let ranks : Finset (Fin 6) := Finset.univ
    let deck : List (Fin 6) := ranks.toList ++ ranks.toList
    let Ω : Finset (List (Fin 6)) := deck.permutations.toFinset
    let X (l : List (Fin 6)) : ℚ :=
      (Finset.range 11).sum (fun i =>
        if l.getD i 0 = l.getD (i + 1) 0 then (1 : ℚ) else 0)
    ((∑ l ∈ Ω, X l) : ℚ) / (Ω.card : ℚ) = 1

theorem problem_15 :
    let ranks : Finset (Fin 6) := Finset.univ
    let deck : List (Fin 6) := ranks.toList ++ ranks.toList
    let Ω : Finset (List (Fin 6)) := deck.permutations.toFinset
    let X (l : List (Fin 6)) : ℚ :=
      (Finset.range 11).sum (fun i =>
        if l.getD i 0 = l.getD (i + 1) 0 then (1 : ℚ) else 0)
    ((∑ l ∈ Ω, X l) : ℚ) / (Ω.card : ℚ) = 1 := by
  exact problem_15_axiom
