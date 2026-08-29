import Mathlib

/-- **Florida lottery.** To be sure of a perfect match one must buy one ticket for
each choice of six numbers out of forty-nine; the number of such choices is
`Nat.choose 49 6`. -/
theorem bona_2 :
    Fintype.card { s : Finset (Fin 49) // s.card = 6 } = Nat.choose 49 6 := by
  simp [Fintype.card_finset_len]
