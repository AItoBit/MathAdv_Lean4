import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

theorem problem_35
  (P : MeasureTheory.Measure ℕ) [MeasureTheory.IsProbabilityMeasure P] :
  ¬ (∀ n m : ℕ, P {n} = P {m}) := by
  intro h
  
  -- The probability of any singleton equals the probability of {0}.
  have h0 : ∀ n, P {n} = P {0} := fun n => h n 0
  
  -- The measure of the universe is the sum of the measures of all singletons.
  have h1 : P Set.univ = ∑' n : ℕ, P {n} := by
    have h_univ : (Set.univ : Set ℕ) = ⋃ n, {n} := by ext x; simp
    rw [h_univ]
    apply measure_iUnion
    · intro i j hij
      exact Set.disjoint_singleton.mpr hij
    · intro i
      exact MeasurableSet.singleton i
      
  -- The measure of the universe for a probability measure is 1.
  have h2 : P Set.univ = 1 := measure_univ
  rw [h2] at h1
  
  -- Substitute P {n} with P {0} in the infinite sum.
  have h3 : ∑' n : ℕ, P {n} = ∑' n : ℕ, P {0} := tsum_congr h0
  rw [h3] at h1
  
  -- The infinite sum of a constant in ENNReal is either 0 (if the constant is 0) or ⊤.
  have h4 : ∑' n : ℕ, P {0} = 0 ∨ ∑' n : ℕ, P {0} = ⊤ := by
    by_cases hc : P {0} = 0
    · left
      rw [hc, tsum_zero]
    · right
      exact ENNReal.tsum_const_eq_top_of_ne_zero hc
      
  -- Both cases contradict the fact that the sum must equal 1.
  rcases h4 with h_zero | h_top
  · rw [h_zero] at h1
    revert h1
    simp
  · rw [h_top] at h1
    revert h1
    simp
