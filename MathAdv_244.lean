import Mathlib

open MeasureTheory

/-- Teorema (probabilities_4_9, Q244 / problem_17):
    Si se elige un punto uniforme en [0, 1], la probabilidad de que x > 1/2
    dado que x < 3/4 es 1/3. -/
theorem problem_17 :
    let μ : MeasureTheory.Measure ℝ :=
      MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)
    let A : Set ℝ := Set.Ioi (1 / 2 : ℝ)
    let B : Set ℝ := Set.Iio (3 / 4 : ℝ)
    (μ (A ∩ B)).toReal / (μ B).toReal = 1 / 3 := by
  intro μ A B
  dsimp [μ, A, B]

  -- 1) Calculamos μ B = volume (Set.Ico 0 (3/4))
  have hB_inter : Set.Icc (0 : ℝ) 1 ∩ Set.Iio (3 / 4 : ℝ) = Set.Ico 0 (3 / 4 : ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h0, _⟩, h34⟩
      exact ⟨h0, h34⟩
    · rintro ⟨h0, h34⟩
      refine ⟨⟨h0, by linarith⟩, h34⟩

  have hμB : (Measure.restrict volume (Set.Icc (0 : ℝ) 1)) (Set.Iio (3 / 4 : ℝ))
      = ENNReal.ofReal (3 / 4) := by
    rw [Measure.restrict_apply (measurableSet_Iio)]
    rw [Set.inter_comm, hB_inter]
    rw [Real.volume_Ico]
    norm_num

  -- 2) Calculamos μ (A ∩ B) = volume (Set.Ioo (1/2) (3/4))
  have hAB_inter : Set.Icc (0 : ℝ) 1 ∩ (Set.Ioi (1 / 2 : ℝ) ∩ Set.Iio (3 / 4 : ℝ))
      = Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨_, ⟨h12, h34⟩⟩
      exact ⟨h12, h34⟩
    · rintro ⟨h12, h34⟩
      refine ⟨⟨by linarith, by linarith⟩, ⟨h12, h34⟩⟩

  have h_meas_AB : MeasurableSet (Set.Ioi (1 / 2 : ℝ) ∩ Set.Iio (3 / 4 : ℝ)) :=
    measurableSet_Ioi.inter measurableSet_Iio

  have hμAB : (Measure.restrict volume (Set.Icc (0 : ℝ) 1)) (Set.Ioi (1 / 2 : ℝ) ∩ Set.Iio (3 / 4 : ℝ))
      = ENNReal.ofReal (1 / 4) := by
    rw [Measure.restrict_apply h_meas_AB]
    rw [Set.inter_comm, hAB_inter]
    rw [Real.volume_Ioo]
    norm_num

  -- 3) Evaluamos el cociente
  rw [hμB, hμAB]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  norm_num
