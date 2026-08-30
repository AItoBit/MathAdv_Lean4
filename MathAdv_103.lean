import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Real Set Filter Topology Function

namespace DirichletIntegral

/-- For `x > 0`, `∫_0^∞ e^{-tx} dt = 1/x`. -/
lemma integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
  have h := integral_comp_mul_right_Ioi (fun u : ℝ => Real.exp (-u)) 0 hx
  simp only [zero_mul, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
  rw [h]; ring

/-- The elementary antiderivative computation `∫_0^r e^{-tx} sin x dx`. -/
lemma integral_exp_neg_mul_sin (t r : ℝ) :
    ∫ x in (0 : ℝ)..r, Real.exp (-(t * x)) * Real.sin x
      = (1 - Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r)) / (1 + t ^ 2) := by
  have ht : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  set F : ℝ → ℝ := fun x => -Real.exp (-(t * x)) * (t * Real.sin x + Real.cos x) / (1 + t ^ 2)
    with hF
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) r, HasDerivAt F (Real.exp (-(t * x)) * Real.sin x) x := by
    intro x _
    have h_lin : HasDerivAt (fun y : ℝ => -(t * y)) (-t) x := by
      have h1 := (hasDerivAt_id x).const_mul (-t)
      have heq : (fun y : ℝ => -t * y) = (fun y : ℝ => -(t * y)) := by ext y; ring
      rwa [heq] at h1
    have h1_pos : HasDerivAt (fun y : ℝ => Real.exp (-(t * y))) (-t * Real.exp (-(t * x))) x :=
      (Real.hasDerivAt_exp (-(t * x))).comp x h_lin
    have h1 : HasDerivAt (fun y : ℝ => -Real.exp (-(t * y))) (t * Real.exp (-(t * x))) x := by
      have h_neg := h1_pos.const_mul (-1)
      have heq_fn : (fun y : ℝ => -1 * Real.exp (-(t * y))) = (fun y : ℝ => -Real.exp (-(t * y))) := by
        ext y; ring
      have heq_d : -1 * (-t * Real.exp (-(t * x))) = t * Real.exp (-(t * x)) := by ring
      rwa [heq_fn, heq_d] at h_neg
    have h2 : HasDerivAt (fun y : ℝ => t * Real.sin y + Real.cos y)
        (t * Real.cos x - Real.sin x) x := by
      have h_sin := (Real.hasDerivAt_sin x).const_mul t
      have h_cos := Real.hasDerivAt_cos x
      have h_add := h_sin.add h_cos
      have heq_d : t * Real.cos x + -Real.sin x = t * Real.cos x - Real.sin x := by ring
      rwa [heq_d] at h_add
    have h_prod := (h1.mul h2).div_const (1 + t ^ 2)
    have heq_fn : (fun y : ℝ => (fun y => -Real.exp (-(t * y))) y * (fun y => t * Real.sin y + Real.cos y) y / (1 + t ^ 2)) = F := by
      ext y; rfl
    have heq_deriv : (t * Real.exp (-(t * x)) * (t * Real.sin x + Real.cos x) +
        -Real.exp (-(t * x)) * (t * Real.cos x - Real.sin x)) / (1 + t ^ 2)
        = Real.exp (-(t * x)) * Real.sin x := by
      have h_alg : (t * Real.exp (-(t * x)) * (t * Real.sin x + Real.cos x) +
        -Real.exp (-(t * x)) * (t * Real.cos x - Real.sin x))
        = Real.exp (-(t * x)) * Real.sin x * (1 + t ^ 2) := by ring
      rw [h_alg, mul_div_cancel_right₀ _ ht]
    rwa [heq_fn, heq_deriv] at h_prod
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [hF, mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

/-- Joint integrability of `(x,t) ↦ e^{-tx} sin x` on `(0,r] × (0,∞)`. -/
lemma integrable_uncurry (r : ℝ) :
    Integrable (uncurry (fun (x t : ℝ) => Real.exp (-(t * x)) * Real.sin x))
      ((volume.restrict (Ioc 0 r)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable
      (uncurry (fun (x t : ℝ) => Real.exp (-(t * x)) * Real.sin x))
      ((volume.restrict (Ioc 0 r)).prod (volume.restrict (Ioi 0))) := by
    apply Continuous.aestronglyMeasurable
    unfold uncurry
    fun_prop
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hx0
    simpa [uncurry, mul_comm, neg_mul] using this.mul_const (Real.sin x)
  · have h1 : Integrable (fun x : ℝ => |Real.sin x| / x) (volume.restrict (Ioc 0 r)) := by
      have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 r) := by
        simp [IntegrableOn]
      refine Integrable.mono' hconst
        ((Real.continuous_sin.abs.measurable).div measurable_id).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_abs, div_le_one hx0]
      simpa [abs_of_pos hx0] using Real.abs_sin_le_abs (x := x)
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hsplit : ∫ t in Ioi (0 : ℝ), ‖Real.exp (-(t * x)) * Real.sin x‖
        = (∫ t in Ioi (0 : ℝ), Real.exp (-(t * x))) * |Real.sin x| := by
      rw [← integral_mul_const]
      congr 1; ext t
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simp only [uncurry]
    rw [hsplit, integral_exp_neg_mul_Ioi hx0]
    ring

/-- The elementary bound `(t+1)/(1+t²) ≤ 2`. -/
lemma aux_bound (t : ℝ) : (t + 1) / (1 + t ^ 2) ≤ 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * t - 1)]

/-- The error term appearing after the Fubini computation. -/
noncomputable def errTerm (r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r) / (1 + t ^ 2)

lemma integrable_errIntegrand {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r) / (1 + t ^ 2))
      (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => 2 * Real.exp (-r * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hr).const_mul 2
  have hcont : Continuous
      (fun t : ℝ => Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r) / (1 + t ^ 2)) := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hnum : |t * Real.sin r + Real.cos r| ≤ t + 1 := by
    have h1 : |t * Real.sin r| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht0]
      nlinarith [Real.abs_sin_le_one r, abs_nonneg (Real.sin r)]
    have h2 : |Real.cos r| ≤ 1 := Real.abs_cos_le_one r
    calc |t * Real.sin r + Real.cos r| ≤ |t * Real.sin r| + |Real.cos r| := abs_add_le _ _
      _ ≤ t + 1 := by linarith
  have : ‖Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r) / (1 + t ^ 2)‖
      = Real.exp (-(t * r)) * (|t * Real.sin r + Real.cos r| / (1 + t ^ 2)) := by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos hden, mul_div_assoc]
  rw [this]
  have hle : |t * Real.sin r + Real.cos r| / (1 + t ^ 2) ≤ 2 :=
    le_trans (by gcongr) (aux_bound t)
  have hexp : Real.exp (-(t * r)) = Real.exp (-r * t) := by ring_nf
  rw [hexp]
  nlinarith [Real.exp_pos (-r * t), abs_nonneg (t * Real.sin r + Real.cos r)]

/-- Main identity: for `r > 0`, `∫_0^r (sin x)/x dx = π/2 - errTerm r`. -/
lemma integral_sin_div_eq (r : ℝ) (hr : 0 < r) :
    ∫ x in (0 : ℝ)..r, Real.sin x / x = π / 2 - errTerm r := by
  have hswap := integral_integral_swap
    (f := fun (x t : ℝ) => Real.exp (-(t * x)) * Real.sin x) (integrable_uncurry r)
  -- left-hand side of the swap
  have hL : (∫ x in Ioc (0 : ℝ) r, ∫ t in Ioi (0 : ℝ), Real.exp (-(t * x)) * Real.sin x)
      = ∫ x in Ioc (0 : ℝ) r, Real.sin x / x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    rw [integral_mul_const, integral_exp_neg_mul_Ioi hx0]
    ring
  -- right-hand side of the swap
  have hR : (∫ t in Ioi (0 : ℝ), ∫ x in Ioc (0 : ℝ) r, Real.exp (-(t * x)) * Real.sin x)
      = ∫ t in Ioi (0 : ℝ),
          (1 - Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r)) / (1 + t ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [← intervalIntegral.integral_of_le hr.le, integral_exp_neg_mul_sin t r]
  rw [hL, hR] at hswap
  rw [intervalIntegral.integral_of_le hr.le, hswap]
  have hsplit : (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r)) / (1 + t ^ 2))
      = (∫ t in Ioi (0 : ℝ), (1 + t ^ 2)⁻¹) - errTerm r := by
    rw [errTerm, ← integral_sub]
    · refine integral_congr_ae ?_
      filter_upwards with t
      field_simp
    · exact integrable_inv_one_add_sq.integrableOn
    · exact integrable_errIntegrand hr
  rw [hsplit, integral_Ioi_inv_one_add_sq]
  simp

lemma errTerm_bound {r : ℝ} (hr : 0 < r) : |errTerm r| ≤ 2 / r := by
  have hg : IntegrableOn (fun t : ℝ => 2 * Real.exp (-r * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hr).const_mul 2
  have hbound : ‖errTerm r‖ ≤ ∫ t in Ioi (0 : ℝ), 2 * Real.exp (-r * t) := by
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hnum : |t * Real.sin r + Real.cos r| ≤ t + 1 := by
      have h1 : |t * Real.sin r| ≤ t := by
        rw [abs_mul, abs_of_nonneg ht0]
        nlinarith [Real.abs_sin_le_one r, abs_nonneg (Real.sin r)]
      have h2 : |Real.cos r| ≤ 1 := Real.abs_cos_le_one r
      calc |t * Real.sin r + Real.cos r| ≤ |t * Real.sin r| + |Real.cos r| := abs_add_le _ _
        _ ≤ t + 1 := by linarith
    have heq : ‖Real.exp (-(t * r)) * (t * Real.sin r + Real.cos r) / (1 + t ^ 2)‖
        = Real.exp (-(t * r)) * (|t * Real.sin r + Real.cos r| / (1 + t ^ 2)) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos hden, mul_div_assoc]
    rw [heq]
    have hle : |t * Real.sin r + Real.cos r| / (1 + t ^ 2) ≤ 2 :=
      le_trans (by gcongr) (aux_bound t)
    have hexp : Real.exp (-(t * r)) = Real.exp (-r * t) := by ring_nf
    rw [hexp]
    nlinarith [Real.exp_pos (-r * t), abs_nonneg (t * Real.sin r + Real.cos r)]
  have hval : (∫ t in Ioi (0 : ℝ), 2 * Real.exp (-r * t)) = 2 / r := by
    rw [integral_const_mul]
    have : (∫ t in Ioi (0 : ℝ), Real.exp (-r * t)) = 1 / r := by
      have := integral_exp_neg_mul_Ioi hr
      simpa [mul_comm] using this
    rw [this]; ring
  rw [hval] at hbound
  simpa using hbound

lemma tendsto_errTerm : Tendsto errTerm atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun r : ℝ => 2 / r) ?_
    (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simpa using errTerm_bound hr

end DirichletIntegral

/-- **The Dirichlet integral**: `∫_0^∞ (sin x)/x dx = π/2`, in the sense that the
truncated integrals `∫_0^r (sin x)/x dx` converge to `π/2` as `r → ∞`. -/
theorem stein_13 :
    Filter.Tendsto (fun r : ℝ => ∫ x in (0 : ℝ)..r, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := by
  have h : Tendsto (fun r : ℝ => π / 2 - DirichletIntegral.errTerm r) atTop (𝓝 (π / 2)) := by
    simpa using tendsto_const_nhds.sub DirichletIntegral.tendsto_errTerm
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (DirichletIntegral.integral_sin_div_eq r hr).symm
