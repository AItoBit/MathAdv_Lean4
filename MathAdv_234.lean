import Mathlib

/-- Teorema (probabilities_4_9, Q234 / problem_7):
    Independencia de los eventos "Cara en la primera moneda" y "Cruz en la segunda moneda"
    en el espacio muestral equiprobable finito Bool × Bool. -/
theorem problem_7 :
    let Ω : Finset (Bool × Bool) := Finset.univ
    let prob : Finset (Bool × Bool) → ℝ := fun E => (E.card : ℝ) / Ω.card
    let A : Finset (Bool × Bool) := Ω.filter (fun ω => ω.1 = true)
    let B : Finset (Bool × Bool) := Ω.filter (fun ω => ω.2 = false)
    prob (A ∩ B) = prob A * prob B := by
  dsimp
  have hΩ : Fintype.card (Bool × Bool) = 4 := by decide
  have hA : ((Finset.univ : Finset (Bool × Bool)).filter (fun ω => ω.1 = true)).card = 2 := by decide
  have hB : ((Finset.univ : Finset (Bool × Bool)).filter (fun ω => ω.2 = false)).card = 2 := by decide
  have hAB : (((Finset.univ : Finset (Bool × Bool)).filter (fun ω => ω.1 = true)) ∩
              ((Finset.univ : Finset (Bool × Bool)).filter (fun ω => ω.2 = false))).card = 1 := by decide
  rw [hΩ, hA, hB, hAB]
  norm_num
