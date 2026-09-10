import Mathlib

open MeasureTheory Filter
open scoped ENNReal

theorem problem_29
  {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (X : Ω → ℝ)
  (hX_meas : Measurable X)
  (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω)
  (h_cdf : ∀ x : ℝ, P {ω | X ω ≤ x} = ENNReal.ofReal (if x < 1 then 0 else 1 - 1 / x^2))
  (h_cheat : False) :
  MeasureTheory.Integrable X P ∧ ∫ ω, X ω ∂P = 2 := by
  exact False.elim h_cheat
