import Mathlib

open Filter Topology

/-- The limit of `(4 - 5x²)/(6x² + 2x)` as `x → ∞` is `-5/6`.
This is computed with the quotient law for limits, after dividing
numerator and denominator by `x²`. -/
theorem dawkins_2_7_3c :
    Filter.Tendsto (fun x : ℝ => (4 - 5 * x^2) / (6 * x^2 + 2 * x)) atTop (𝓝 (-5 / 6 : ℝ)) := by
  have h4 : Tendsto (fun x : ℝ => 4 / x ^ 2 - 5) atTop (𝓝 (0 - 5)) := by
    exact (tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))).sub tendsto_const_nhds
  have h6 : Tendsto (fun x : ℝ => 6 + 2 / x) atTop (𝓝 (6 + 0)) := by
    exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  have hd : Tendsto (fun x : ℝ => (4 / x ^ 2 - 5) / (6 + 2 / x)) atTop (𝓝 ((0 - 5) / (6 + 0))) :=
    h4.div h6 (by norm_num)
  have hd' : Tendsto (fun x : ℝ => (4 / x ^ 2 - 5) / (6 + 2 / x)) atTop (𝓝 (-5 / 6 : ℝ)) := by
    simpa using hd
  refine hd'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
