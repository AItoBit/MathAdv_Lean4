import Mathlib

open Real intervalIntegral

/-- The derivative of `x ↦ x * log (x² + 1) - 2x + 2 arctan x` is `log (x² + 1)`. -/
lemma hasDerivAt_antideriv (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.log (t ^ 2 + 1) - 2 * t + 2 * Real.arctan t)
      (Real.log (x ^ 2 + 1)) x := by
  have hpos : (0:ℝ) < x ^ 2 + 1 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).add_const 1)
  have h2 : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + 1)) ((2 * x) / (x ^ 2 + 1)) x :=
    h1.log (ne_of_gt hpos)
  have h3 : HasDerivAt (fun t : ℝ => t * Real.log (t ^ 2 + 1))
      (1 * Real.log (x ^ 2 + 1) + x * ((2 * x) / (x ^ 2 + 1))) x :=
    (hasDerivAt_id x).mul h2
  have h4 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h5 : HasDerivAt (fun t : ℝ => 2 * Real.arctan t) (2 * (1 / (1 + x ^ 2))) x :=
    (Real.hasDerivAt_arctan x).const_mul 2
  have := (h3.sub h4).add h5
  convert this using 1
  field_simp
  ring

/-- `∫₀³ log(x²+1) dx = 3 log 10 - 6 + 2 arctan 3`. -/
theorem strang_7_1_32 :
    ∫ x in (0 : ℝ)..(3 : ℝ), Real.log (x ^ 2 + 1) =
      3 * Real.log 10 - 6 + 2 * Real.arctan 3 := by
  have hcont : IntervalIntegrable (fun x : ℝ => Real.log (x ^ 2 + 1)) MeasureTheory.volume 0 3 := by
    apply Continuous.intervalIntegrable
    exact (by continuity : Continuous fun x : ℝ => x ^ 2 + 1).log (fun x => by positivity)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t * Real.log (t ^ 2 + 1) - 2 * t + 2 * Real.arctan t)
    (fun x _ => hasDerivAt_antideriv x) hcont
  rw [this]
  norm_num
