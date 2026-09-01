import Mathlib

/-- Teorema (probabilities_4_9, Q237 / problem_10):
    Cálculo de la probabilidad posterior según el Teorema de Bayes
    al extraer una carta común entre dos barajas (una completa de 52 cartas
    y una incompleta de 51 cartas). -/
theorem problem_10
    (prob_choose_deck : ℝ) (h_choose : prob_choose_deck = 1 / 2)
    (size_complete : ℕ) (h_complete : size_complete = 52)
    (size_incomplete : ℕ) (h_incomplete : size_incomplete = 51) :
    let p_card_given_complete : ℝ := 1 / (size_complete : ℝ)
    let p_card_given_incomplete : ℝ := 1 / (size_incomplete : ℝ)
    let p_card_total : ℝ :=
      p_card_given_complete * prob_choose_deck + p_card_given_incomplete * prob_choose_deck
    (p_card_given_complete * prob_choose_deck) / p_card_total = 51 / 103 := by
  intro p_card_given_complete p_card_given_incomplete p_card_total
  dsimp [p_card_total, p_card_given_complete, p_card_given_incomplete]
  rw [h_choose, h_complete, h_incomplete]
  norm_num
