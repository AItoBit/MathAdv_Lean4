import Mathlib

open Real

/--
**Cooling of a semi-infinite solid.**

A semi-infinite solid `x ≥ 0`, initially at a uniform temperature, whose boundary plane
`x = 0` is kept at a constant temperature, has a temperature distribution that depends on
`x` and `t` only through the similarity variable `x / √t`, i.e. `u x t = F (x / √t)`
(here `F` absorbs the diffusivity constant).  Assuming `F` is injective on positive
arguments, the times required for two interior points to reach a common temperature `θ`
are proportional to the squares of their distances from the boundary plane.
-/
theorem brown_4
  {F : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
  (h_def : ∀ x t, 0 < t → u x t = F (x / sqrt t))
  (hF_inj_pos : ∀ a b, 0 < a → 0 < b → F a = F b → a = b)
  {x1 x2 t1 t2 θ : ℝ}
  (hx1 : 0 < x1) (hx2 : 0 < x2) (ht1 : 0 < t1) (ht2 : 0 < t2)
  (heq1 : u x1 t1 = θ) (heq2 : u x2 t2 = θ) :
  t1 / t2 = (x1 / x2) ^ 2 := by
  have hs1 : 0 < Real.sqrt t1 := Real.sqrt_pos.mpr ht1
  have hs2 : 0 < Real.sqrt t2 := Real.sqrt_pos.mpr ht2
  have hFeq : F (x1 / Real.sqrt t1) = F (x2 / Real.sqrt t2) := by
    rw [← h_def x1 t1 ht1, ← h_def x2 t2 ht2, heq1, heq2]
  have key : x1 / Real.sqrt t1 = x2 / Real.sqrt t2 :=
    hF_inj_pos _ _ (div_pos hx1 hs1) (div_pos hx2 hs2) hFeq
  have hcross : x1 * Real.sqrt t2 = x2 * Real.sqrt t1 := by
    field_simp at key
    linarith [key]
  have hsq : x1 ^ 2 * t2 = x2 ^ 2 * t1 := by
    have := congrArg (fun z : ℝ => z ^ 2) hcross
    simp only [mul_pow, Real.sq_sqrt ht1.le, Real.sq_sqrt ht2.le] at this
    exact this
  field_simp
  linarith [hsq]
