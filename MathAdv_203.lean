import Mathlib

open scoped BigOperators
open scoped Topology
open scoped Real

theorem Manin_Zilber_13
    {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    let l1 : (Fin n → ℝ) → ℝ := fun x => ∑ i, |x i|
    let pEval : (Fin n → ℝ) → ℝ := fun x => MvPolynomial.eval x p
    let f : ℝ → ℝ := fun r => sInf (pEval '' {x | l1 x = r})
    (hunbdd : ∀ R > 0, ∃ rR : ℝ, ∀ r : ℝ, r > rR → f r > R) →
    ∃ a : ℚ, 0 < (a : ℝ) ∧ ∃ c : ℝ, 0 < c ∧
      Filter.Tendsto (fun r : ℝ => r ^ (-(a : ℝ)) * f r) Filter.atTop (nhds c) := by
  sorry
