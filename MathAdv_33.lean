import Mathlib

open Filter

/-- For `f x = eˣ / x⁵`, we have `lim_{x → ∞} f x = ∞`. -/
theorem dawkins_4_10_c :
    Filter.Tendsto (fun x : ℝ => Real.exp x / x ^ 5) atTop atTop :=
  Real.tendsto_exp_div_pow_atTop 5
