import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q276 / real_analysis_11):
    Si una serie de términos no negativos ∑ a_n converge, entonces ∑ a_n^2 también converge. -/
theorem real_analysis_11 {a : ℕ → ℝ}
    (h_nonneg : ∀ n, 0 ≤ a n)
    (h_sum : Summable a) :
    Summable (fun n => (a n)^2) := by
  let S := ∑' n, a n
  have h_le_S : ∀ n, a n ≤ S := by
    intro n
    exact le_hasSum h_sum.hasSum n (fun i _ => h_nonneg i)
  have h_le : ∀ n, (a n)^2 ≤ S * a n := by
    intro n
    rw [sq]
    exact mul_le_mul_of_nonneg_right (h_le_S n) (h_nonneg n)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg (a n)) h_le ?_
  exact h_sum.mul_left S
