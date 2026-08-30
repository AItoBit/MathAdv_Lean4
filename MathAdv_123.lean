import Mathlib

open MeasureTheory Filter Topology

/-- The truncation `f_L` agrees with the indicator of `f` on the set `{x | |x| ≤ L}`. -/
lemma truncation_eq_indicator (f : ℝ → ℂ) (f_L : ℝ → ℝ → ℂ)
    (h_def : ∀ (L x : ℝ), f_L L x = if |x| ≤ L then f x else 0) (L : ℝ) :
    f_L L = Set.indicator {x : ℝ | |x| ≤ L} f := by
  funext x
  rw [h_def]
  by_cases hx : |x| ≤ L <;> simp [hx]

/-- The set `{x | |x| ≤ L}` is measurable. -/
lemma measurableSet_abs_le (L : ℝ) : MeasurableSet {x : ℝ | |x| ≤ L} :=
  measurableSet_le (by fun_prop) measurable_const

/-- Each truncation is integrable. -/
lemma truncation_integrable (f : ℝ → ℂ) (hf : Integrable f volume) (f_L : ℝ → ℝ → ℂ)
    (h_def : ∀ (L x : ℝ), f_L L x = if |x| ≤ L then f x else 0) (L : ℝ) :
    Integrable (f_L L) volume := by
  rw [truncation_eq_indicator f f_L h_def L]
  exact hf.indicator (measurableSet_abs_le L)

/-- Pointwise, the error `‖f_L L x - f x‖` vanishes for `L` large. -/
lemma truncation_error_tendsto (f : ℝ → ℂ) (f_L : ℝ → ℝ → ℂ)
    (h_def : ∀ (L x : ℝ), f_L L x = if |x| ≤ L then f x else 0) (x : ℝ) :
    Tendsto (fun L => ‖f_L L x - f x‖) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  filter_upwards [eventually_ge_atTop |x|] with L hL
  simp [h_def L x, hL]

/-- `f_L` is integrable for every `L > 0`, and `∫ ‖f_L - f‖ → 0` as `L → ∞`. -/
theorem melrose_sp2009_3
  (f : ℝ → ℂ) (hf : MeasureTheory.Integrable f volume)
  (f_L : ℝ → ℝ → ℂ)
  (h_def : ∀ (L x : ℝ), f_L L x = if |x| ≤ L then f x else 0) :
  (∀ L > 0, MeasureTheory.Integrable (f_L L) volume) ∧
  Filter.Tendsto (fun L => ∫ x, ‖f_L L x - f x‖ ∂volume) Filter.atTop (𝓝 0) := by
  refine ⟨fun L _ => truncation_integrable f hf f_L h_def L, ?_⟩
  have key : Tendsto (fun L => ∫ x, ‖f_L L x - f x‖ ∂volume) atTop
      (𝓝 (∫ _x : ℝ, (0 : ℝ) ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      (.of_forall fun L => ?_) (.of_forall fun L => ?_) hf.norm
      (.of_forall (truncation_error_tendsto f f_L h_def))
    · exact (((truncation_integrable f hf f_L h_def L).sub hf).aestronglyMeasurable).norm
    · filter_upwards with x
      rw [h_def L x]
      by_cases hx : |x| ≤ L <;> simp [hx]
  simpa using key
