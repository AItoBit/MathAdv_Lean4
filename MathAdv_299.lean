import Mathlib

open Set

theorem r3_minus_zero_deformation_retract :
  ∃ H :
      ContinuousMap
        ({x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1)
        ({x : (Fin 3 → ℝ) // x ≠ 0}),
    (∀ x, H (x, ⟨0, by simp⟩) = x) ∧
    (∀ x, ‖(H (x, ⟨1, by simp⟩)).1‖ = 1) ∧
    (∀ x : {x : (Fin 3 → ℝ) // x ≠ 0},
        ‖x.1‖ = 1 →
        ∀ t : Set.Icc (0 : ℝ) 1,
          H (x, t) = x) := by

  have hnorm_inv :
      Continuous
        (fun x : {x : (Fin 3 → ℝ) // x ≠ 0} =>
          ‖x.1‖⁻¹) := by
    have hn :
        Continuous
          (fun x : {x : (Fin 3 → ℝ) // x ≠ 0} =>
            ‖x.1‖) := by
      exact continuous_norm.comp continuous_subtype_val

    apply hn.inv₀
    intro x
    exact norm_ne_zero_iff.mpr x.property

  have ht :
      Continuous
        (fun p :
            {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1 =>
          (p.2.1 : ℝ)) := by
    exact continuous_subtype_val.comp continuous_snd

  have hx :
      Continuous
        (fun p :
            {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1 =>
          (p.1.1 : Fin 3 → ℝ)) := by
    exact continuous_subtype_val.comp continuous_fst

  have hinv :
      Continuous
        (fun p :
            {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1 =>
          ‖p.1.1‖⁻¹) := by
    exact hnorm_inv.comp continuous_fst

  have hfactor :
      Continuous
        (fun p :
            {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1 =>
          (1 - (p.2.1 : ℝ)) +
            (p.2.1 : ℝ) * ‖p.1.1‖⁻¹) := by
    exact
      (continuous_const.sub ht).add
        (ht.mul hinv)

  have hvec :
      Continuous
        (fun p :
            {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1 =>
          ((1 - (p.2.1 : ℝ)) +
              (p.2.1 : ℝ) * ‖p.1.1‖⁻¹) •
            p.1.1) := by
    exact hfactor.smul hx

  have hnonzero :
      ∀ p :
          {x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1,
        ((1 - (p.2.1 : ℝ)) +
            (p.2.1 : ℝ) * ‖p.1.1‖⁻¹) •
          p.1.1 ≠ 0 := by
    intro p

    have hxnorm :
        0 < ‖p.1.1‖ := by
      exact norm_pos_iff.mpr p.1.property

    have hinvpos :
        0 < ‖p.1.1‖⁻¹ := by
      exact inv_pos.mpr hxnorm

    have ht0 :
        0 ≤ (p.2.1 : ℝ) :=
      p.2.property.1

    have ht1 :
        (p.2.1 : ℝ) ≤ 1 :=
      p.2.property.2

    have hcoef :
        0 <
          (1 - (p.2.1 : ℝ)) +
            (p.2.1 : ℝ) * ‖p.1.1‖⁻¹ := by
      by_cases hteq : (p.2.1 : ℝ) = 1

      · rw [hteq]
        simpa using hinvpos

      · have hlt :
            (p.2.1 : ℝ) < 1 := by
          exact lt_of_le_of_ne ht1 hteq

        have hsecond :
            0 ≤
              (p.2.1 : ℝ) *
                ‖p.1.1‖⁻¹ := by
          exact mul_nonneg ht0 (le_of_lt hinvpos)

        linarith

    exact smul_ne_zero (ne_of_gt hcoef) p.1.property

  let Hfun :
      ({x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1) →
        {x : (Fin 3 → ℝ) // x ≠ 0} :=
    fun p =>
      ⟨
        ((1 - (p.2.1 : ℝ)) +
            (p.2.1 : ℝ) * ‖p.1.1‖⁻¹) •
          p.1.1,
        hnonzero p
      ⟩

  have hHfun :
      Continuous Hfun := by
    dsimp [Hfun]
    exact hvec.subtype_mk hnonzero

  let H :
      ContinuousMap
        ({x : (Fin 3 → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1)
        ({x : (Fin 3 → ℝ) // x ≠ 0}) :=
    ⟨Hfun, hHfun⟩

  refine ⟨H, ?_, ?_, ?_⟩

  · -- H(x,0) = x
    intro x
    apply Subtype.ext

    change
      ((1 - (0 : ℝ)) +
          (0 : ℝ) * ‖x.1‖⁻¹) •
        x.1 = x.1

    simp

  · -- H(x,1) lies on S²
    intro x

    have hxnorm :
        0 < ‖x.1‖ := by
      exact norm_pos_iff.mpr x.property

    have hxnorm_ne :
        ‖x.1‖ ≠ 0 :=
      ne_of_gt hxnorm

    change
      ‖((1 - (1 : ℝ)) +
          (1 : ℝ) * ‖x.1‖⁻¹) •
        x.1‖ = 1

    simp only [sub_self, zero_add, one_mul]

    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]

    exact inv_mul_cancel₀ hxnorm_ne

  · -- Points already on S² remain fixed throughout the homotopy.
    intro x hxnorm t
    apply Subtype.ext

    change
      ((1 - (t.1 : ℝ)) +
          (t.1 : ℝ) * ‖x.1‖⁻¹) •
        x.1 = x.1

    have hcoef :
        (1 - (t.1 : ℝ)) +
            (t.1 : ℝ) * ‖x.1‖⁻¹ = 1 := by
      rw [hxnorm]
      norm_num
      ring

    rw [hcoef]
    exact one_smul ℝ x.1
