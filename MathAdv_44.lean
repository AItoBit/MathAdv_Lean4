import Mathlib

open Real intervalIntegral

/-- On `[0, π/4]` the cosine is positive. -/
lemma cos_pos_of_mem_uIcc_zero_pi_div_four {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) (Real.pi / 4)) :
    0 < Real.cos x := by
  rw [Set.uIcc_of_le (by positivity)] at hx
  obtain ⟨h0, h1⟩ := hx
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The derivative of `sec θ = 1 / cos θ` is `sin θ / cos θ ^ 2`. -/
lemma deriv_one_div_cos {x : ℝ} (hx : Real.cos x ≠ 0) :
    deriv (fun θ : ℝ => 1 / Real.cos θ) x = Real.sin x / (Real.cos x) ^ 2 := by
  have h_num := hasDerivAt_const x (1 : ℝ)
  have h_den := Real.hasDerivAt_cos x
  have h_div := h_num.div h_den hx
  have h : HasDerivAt (fun θ : ℝ => 1 / Real.cos θ) (Real.sin x / (Real.cos x) ^ 2) x := by
    apply HasDerivAt.congr_deriv h_div
    ring
  exact h.deriv

/-- The integrand of the polar arc-length formula for `r = sec θ` equals `1 / cos θ ^ 2`. -/
lemma polar_arclength_integrand {x : ℝ} (hx : Real.cos x ≠ 0) :
    Real.sqrt ((1 / Real.cos x) ^ 2 + (deriv (fun θ : ℝ => 1 / Real.cos θ) x) ^ 2)
      = 1 / (Real.cos x) ^ 2 := by
  rw [deriv_one_div_cos hx]
  have key : (1 / Real.cos x) ^ 2 + (Real.sin x / (Real.cos x) ^ 2) ^ 2
      = (1 / (Real.cos x) ^ 2) ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq x
    field_simp
    nlinarith [hpy, sq_nonneg (Real.cos x), sq_nonneg (Real.sin x)]
  rw [key, Real.sqrt_sq (by positivity)]

/-- `∫ 1/cos²` over `[0, π/4]` equals `1`. -/
lemma integral_one_div_cos_sq_zero_pi_div_four :
    ∫ θ in (0 : ℝ)..(Real.pi / 4 : ℝ), 1 / (Real.cos θ) ^ 2 = 1 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/4),
      HasDerivAt Real.tan (1 / (Real.cos x) ^ 2) x := fun x hx =>
    Real.hasDerivAt_tan (ne_of_gt (cos_pos_of_mem_uIcc_zero_pi_div_four hx))
  have hcont : ContinuousOn (fun x : ℝ => 1 / (Real.cos x) ^ 2) (Set.uIcc (0:ℝ) (Real.pi/4)) := by
    intro x hx
    have := cos_pos_of_mem_uIcc_zero_pi_div_four hx
    exact ContinuousAt.continuousWithinAt
      (by fun_prop (disch := positivity))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [Real.tan_pi_div_four]

/-- **Arc length in polar coordinates.** The length of the curve `r = sec θ`
for `θ` from `0` to `π/4` is `1`. -/
theorem strang_9_3_26 :
    let sec := fun x : ℝ => 1 / Real.cos x
    ∫ θ in (0 : ℝ)..(Real.pi / 4 : ℝ),
        Real.sqrt ((sec θ)^2 + (deriv (fun θ : ℝ => sec θ) θ)^2) = 1 := by
  show ∫ θ in (0 : ℝ)..(Real.pi / 4 : ℝ),
      Real.sqrt ((1 / Real.cos θ)^2 + (deriv (fun θ : ℝ => 1 / Real.cos θ) θ)^2) = 1
  rw [intervalIntegral.integral_congr
    (g := fun x : ℝ => 1 / (Real.cos x) ^ 2)
    (fun x hx => polar_arclength_integrand
      (ne_of_gt (cos_pos_of_mem_uIcc_zero_pi_div_four hx)))]
  exact integral_one_div_cos_sq_zero_pi_div_four
