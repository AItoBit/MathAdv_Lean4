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

open Complex Metric

/-- The curve `C : x² - 10x + y² = 0` is exactly the circle of centre `5` and radius `5`
in the complex plane. -/
theorem curve_eq_sphere :
    {z : ℂ | z.re ^ 2 - 10 * z.re + z.im ^ 2 = 0} = Metric.sphere (5 : ℂ) (5 : ℝ) := by
  ext z
  simp only [Set.mem_ofPred_eq, Metric.mem_sphere, Complex.dist_eq_re_im, Complex.re_ofNat,
    Complex.im_ofNat]
  constructor
  · intro h
    rw [show (z.re - 5) ^ 2 + (z.im - 0) ^ 2 = 5 ^ 2 by nlinarith]
    exact Real.sqrt_sq (by norm_num)
  · intro h
    have h2 := congrArg (fun t : ℝ => t ^ 2) h
    rw [Real.sq_sqrt (by positivity)] at h2
    nlinarith [h2]

/-- The point `1` (a pole of `1/(z² - 1)`) lies inside the circle. -/
theorem one_mem_ball : (1 : ℂ) ∈ Metric.ball (5 : ℂ) 5 := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  norm_num

/-- The auxiliary function `z ↦ 1/(z+1)` is differentiable on the closed disc `|z - 5| ≤ 5`,
since its only singularity `-1` is at distance `6` from the centre. -/
theorem aux_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (z + 1)) (Metric.closedBall (5 : ℂ) 5) := by
  intro z hz
  have hz' : dist z (5 : ℂ) ≤ 5 := Metric.mem_closedBall.mp hz
  have hne : z + 1 ≠ 0 := by
    intro h
    have hz1 : z = -1 := by linear_combination h
    rw [hz1, Complex.dist_eq_re_im] at hz'
    norm_num at hz'
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z + 1) z := differentiableAt_id.add_const 1
  exact ((differentiableAt_const (1 : ℂ)).div h1 hne).differentiableWithinAt

/-- **Cauchy's integral formula** gives `∮_{|z-5|=5} dz/(z² - 1) = πi`: the integral of
`1/(z² - 1)` over the circle `x² - 10x + y² = 0` (counterclockwise) equals `πi`.
Indeed `1/(z² - 1) = (z - 1)⁻¹ · 1/(z + 1)`, the pole `1` lies inside the circle and the
pole `-1` lies outside it, so the integral is `2πi · 1/(1 + 1) = πi`. -/
theorem question_1 :
    (∮ z in C((5 : ℂ), (5 : ℝ)),
        (1 : ℂ) / (z^2 - 1) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
  have key := aux_differentiableOn.circleIntegral_sub_inv_smul one_mem_ball
  have hfun : (fun z : ℂ => (1 : ℂ) / (z ^ 2 - 1))
      = fun z : ℂ => (z - 1)⁻¹ • ((fun w : ℂ => 1 / (w + 1)) z) := by
    funext z
    simp only [smul_eq_mul, one_div]
    rw [← mul_inv]
    congr 1
    ring
  rw [hfun, key]
  simp only [smul_eq_mul]
  rw [show (1 : ℂ) + 1 = 2 by ring]
  field_simp
