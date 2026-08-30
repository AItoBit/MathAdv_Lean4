import Mathlib

/-!
# Compactness of two quartic surfaces (Pressley, Exercise 5.4.1)

The surface `x² - y² + z⁴ = 1` is closed but unbounded, hence not compact,
while the surface `x² + y² + z⁴ = 1` is closed and contained in `[-1,1]³`,
hence compact.
-/

open Set

/-- The hyperboloid-like surface `x² - y² + z⁴ = 1`. -/
def PressleySurface1 : Set (ℝ × ℝ × ℝ) := { p | p.1 ^ 2 - p.2.1 ^ 2 + p.2.2 ^ 4 = 1 }

/-- The ovaloid-like surface `x² + y² + z⁴ = 1`. -/
def PressleySurface2 : Set (ℝ × ℝ × ℝ) := { p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 4 = 1 }

/-- The projection of the first surface onto the `y`-axis is all of `ℝ`:
the surface is unbounded. -/
lemma pressleySurface1_proj_eq_univ :
    (fun p : ℝ × ℝ × ℝ => p.2.1) '' PressleySurface1 = univ := by
  refine eq_univ_of_forall fun y => ⟨(Real.sqrt (1 + y ^ 2), y, 0), ?_, rfl⟩
  have h : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  show Real.sqrt (1 + y ^ 2) ^ 2 - y ^ 2 + (0:ℝ) ^ 4 = 1
  rw [h]; ring

lemma pressleySurface2_isClosed : IsClosed PressleySurface2 := by
  have : Continuous fun p : ℝ × ℝ × ℝ => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 4 := by fun_prop
  simpa [PressleySurface2] using isClosed_eq this continuous_const

lemma pressleySurface2_subset_ball : PressleySurface2 ⊆ Metric.closedBall 0 1 := by
  rintro ⟨x, y, z⟩ h
  have h' : x ^ 2 + y ^ 2 + z ^ 4 = 1 := h
  have hz4 : z ^ 4 ≥ 0 := by positivity
  have hx : |x| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have hy : |y| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg (y - 1), sq_nonneg (y + 1)]
  have hz : |z| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z ^ 2 - 1), sq_nonneg (z - 1),
        sq_nonneg (z + 1), sq_nonneg z]
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
    max_le_iff]
  exact ⟨hx, hy, hz⟩

/-- The surface `x² - y² + z⁴ = 1` is not compact, while `x² + y² + z⁴ = 1` is. -/
theorem Pressley_5_4_1 :
    let S1 : Set (ℝ × (ℝ × ℝ)) := { p | p.1 ^ 2 - p.2.1 ^ 2 + p.2.2 ^ 4 = 1 }
    let S2 : Set (ℝ × (ℝ × ℝ)) := { p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 4 = 1 }
    ¬ IsCompact S1 ∧ IsCompact S2 := by
  intro S1 S2
  constructor
  · intro hc
    have h := hc.image (f := fun p : ℝ × ℝ × ℝ => p.2.1) (by fun_prop)
    rw [show S1 = PressleySurface1 from rfl, pressleySurface1_proj_eq_univ] at h
    exact (noncompact_univ ℝ) h
  · exact Metric.isCompact_of_isClosed_isBounded pressleySurface2_isClosed
      (Metric.isBounded_closedBall.subset pressleySurface2_subset_ball)
