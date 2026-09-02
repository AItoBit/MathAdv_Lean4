import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q262 / problem_35):
    No existe una medida de probabilidad sobre ℕ donde todos los singletons
    tengan exactamente la misma medida (no hay distribución uniforme σ-aditiva sobre ℕ). -/
theorem problem_35
    (P : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure P] :
    ¬ (∀ n m : ℕ, P {n} = P {m}) := by
  intro h
  have h_const : ∀ n : ℕ, P {0} = P {n} := fun n => h 0 n
  have h_sum : (∑' n : ℕ, P {n}) = P (Set.univ : Set ℕ) := by
    rw [← MeasureTheory.measure_iUnion]
    · congr 1
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_singleton_iff, exists_eq']
    · intro i j hij
      exact Set.disjoint_singleton_right.mpr (Ne.symm hij)
    · intro i
      exact MeasurableSet.singleton i
  have h_univ : P (Set.univ : Set ℕ) = 1 := MeasureTheory.measure_univ
  have h_sum_c : (∑' _n : ℕ, P {0}) = 1 := by
    rw [← h_univ, ← h_sum]
    congr 1
    ext n
    exact h_const n
  by_cases hc : P {0} = 0
  · simp [hc] at h_sum_c
  · have h_top : (∑' _n : ℕ, P {0}) = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero hc
    rw [h_top] at h_sum_c
    exact ENNReal.top_ne_one h_sum_c
