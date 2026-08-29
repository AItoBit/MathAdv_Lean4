import Mathlib

/-!
# Positive integers up to 1000 coprime to both 7 and 8

There are exactly `429` positive integers `n ≤ 1000` with `gcd n 7 = 1` and `gcd n 8 = 1`.
This is stated as an equivalence between the corresponding subtype of `ℕ` and `Fin 429`.
-/

namespace RequestProject

/-- The finite set of positive integers `n ≤ 1000` that are coprime to both `7` and `8`. -/
def coprime78 : Finset ℕ :=
  (Finset.Icc 1 1000).filter (fun n => Nat.gcd n 7 = 1 ∧ Nat.gcd n 8 = 1)

theorem mem_coprime78 (n : ℕ) :
    n ∈ coprime78 ↔ 1 ≤ n ∧ n ≤ 1000 ∧ Nat.gcd n 7 = 1 ∧ Nat.gcd n 8 = 1 := by
  simp [coprime78, Finset.mem_filter, Finset.mem_Icc, and_assoc]

set_option maxRecDepth 10000 in
/-- There are `429` such integers. -/
theorem card_coprime78 : coprime78.card = 429 := by
  decide

/-- The number of positive integers not larger than `1000` that are relatively prime to both
`7` and `8` is `429`. -/
theorem bona_5 :
    Nonempty
      ({ n : ℕ // 1 ≤ n ∧ n ≤ 1000 ∧ Nat.gcd n 7 = 1 ∧ Nat.gcd n 8 = 1 } ≃ Fin 429) := by
  classical
  have _inst : Fintype { n : ℕ // 1 ≤ n ∧ n ≤ 1000 ∧ Nat.gcd n 7 = 1 ∧ Nat.gcd n 8 = 1 } :=
    Fintype.subtype coprime78 mem_coprime78
  refine ⟨Fintype.equivFinOfCardEq ?_⟩
  rw [Fintype.card_of_subtype coprime78 mem_coprime78, card_coprime78]

end RequestProject
