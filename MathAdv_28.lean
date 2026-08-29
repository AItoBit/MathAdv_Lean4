import Mathlib

/-- The function `x ↦ 6x²/(4-x)` is not differentiable at `x = 4`
(indeed it is not even continuous there). -/
lemma not_differentiableAt_six_sq_div_four_sub :
    ¬ DifferentiableAt ℝ (fun x : ℝ => 6 * x ^ 2 / (4 - x)) 4 := by
  intro hd
  have hc : ContinuousAt (fun x : ℝ => 6 * x ^ 2 / (4 - x) * (4 - x)) 4 :=
    hd.continuousAt.mul (by fun_prop)
  have h1 : Filter.Tendsto (fun x : ℝ => 6 * x ^ 2 / (4 - x) * (4 - x))
      (nhdsWithin 4 {(4 : ℝ)}ᶜ) (nhds 0) := by
    have := hc.continuousWithinAt (s := {(4 : ℝ)}ᶜ)
    simpa [ContinuousWithinAt] using this
  have heq : Set.EqOn (fun x : ℝ => 6 * x ^ 2 / (4 - x) * (4 - x))
      (fun x : ℝ => 6 * x ^ 2) ({(4 : ℝ)}ᶜ) := by
    intro x hx
    have hx4 : (4 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    field_simp
  have h2 : Filter.Tendsto (fun x : ℝ => 6 * x ^ 2 / (4 - x) * (4 - x))
      (nhdsWithin 4 {(4 : ℝ)}ᶜ) (nhds 96) := by
    have hcont : Filter.Tendsto (fun x : ℝ => 6 * x ^ 2)
        (nhdsWithin 4 {(4 : ℝ)}ᶜ) (nhds 96) := by
      have h0 : ContinuousAt (fun x : ℝ => 6 * x ^ 2) 4 := by fun_prop
      have h1 := h0.tendsto.mono_left (nhdsWithin_le_nhds (s := ({(4 : ℝ)}ᶜ)))
      norm_num at h1
      exact h1
    exact hcont.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heq).symm
  have := tendsto_nhds_unique h1 h2
  norm_num at this

/-- The derivative of `f (x) = 6x²/(4-x)` is `(48x - 6x²)/(4-x)²`.
(At the point `x = 4` both sides equal `0` under Lean's junk-value convention
for division by zero, so the equality of functions holds on all of `ℝ`.) -/
theorem dawkins_3_4_4 :
    deriv (fun x : ℝ => 6 * x ^ 2 / (4 - x)) = fun x => (48 * x - 6 * x ^ 2) / (4 - x) ^ 2 := by
  funext x
  rcases eq_or_ne x 4 with rfl | hx
  · rw [deriv_zero_of_not_differentiableAt not_differentiableAt_six_sq_div_four_sub]
    norm_num
  · have h4 : (4 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hc : HasDerivAt (fun x : ℝ => 6 * x ^ 2) (12 * x) x := by
      have := (hasDerivAt_pow 2 x).const_mul (6 : ℝ)
      convert this using 1
      ring
    have hd : HasDerivAt (fun x : ℝ => 4 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (4 : ℝ)
    have hdiv : HasDerivAt (fun y : ℝ => 6 * y ^ 2 / (4 - y))
        ((12 * x * (4 - x) - 6 * x ^ 2 * (-1)) / (4 - x) ^ 2) x := hc.div hd h4
    rw [hdiv.deriv]
    field_simp
    ring
