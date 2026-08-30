import Mathlib

/-!
# Distance to a subspace and norm-one functionals

Let `Y` be a subspace of a normed space `X` and `x ∈ X`.  Then
`d(x, Y) = inf {‖x - y‖ : y ∈ Y} ≥ 1` if and only if there is a continuous linear
functional `f` in the closed unit ball of `X*` with `Y ⊆ ker f` and `f x = 1`.

The nontrivial direction is a consequence of the Hahn–Banach theorem (here in the
form of the existence of norm-one dual vectors, applied on the quotient `X ⧸ Y`).
-/

open Metric

/-- The canonical projection `X → X ⧸ Y` as a continuous linear map of norm at most `1`. -/
noncomputable def quotientMkCLM {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Submodule ℝ X) : X →L[ℝ] (X ⧸ Y) :=
  Y.mkQ.mkContinuous 1 (fun m => by
    simpa using (Submodule.Quotient.norm_mk_le (S := Y) m))

@[simp]
lemma quotientMkCLM_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Submodule ℝ X) (m : X) :
    quotientMkCLM Y m = Submodule.Quotient.mk m := rfl

lemma norm_quotientMkCLM_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Submodule ℝ X) : ‖quotientMkCLM Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The norm of the class of `x` in `X ⧸ Y` is the distance from `x` to `Y`. -/
lemma norm_quotient_mk_eq_infDist {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Submodule ℝ X) (x : X) :
    ‖(Submodule.Quotient.mk x : X ⧸ Y)‖ = Metric.infDist x (Y : Set X) :=
  QuotientAddGroup.norm_mk (S := Y.toAddSubgroup) x

/-- **Distance to a subspace via dual functionals.**
`d(x, Y) ≥ 1` iff there is `f` in the closed unit ball of the dual with `Y ⊆ ker f`
and `f x = 1`. -/
theorem bollobas_3_14
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Y : Submodule ℝ X) (x : X) :
  (Metric.infDist x (Y : Set X) ≥ 1) ↔
    ∃ (f : X →L[ℝ] ℝ),
      ‖f‖ ≤ 1 ∧
      f x = 1 ∧
      ∀ ⦃y : X⦄, y ∈ Y → f y = 0 := by
  constructor
  · intro hd
    set xq : X ⧸ Y := Submodule.Quotient.mk x with hxq
    have hnorm : ‖xq‖ = Metric.infDist x (Y : Set X) := norm_quotient_mk_eq_infDist Y x
    have hpos : (1 : ℝ) ≤ ‖xq‖ := by rw [hnorm]; exact hd
    obtain ⟨g, hg1, hg2⟩ := exists_dual_vector'' ℝ xq
    refine ⟨(‖xq‖)⁻¹ • (g.comp (quotientMkCLM Y)), ?_, ?_, ?_⟩
    · rw [norm_smul]
      have h1 : ‖g.comp (quotientMkCLM Y)‖ ≤ 1 := by
        calc ‖g.comp (quotientMkCLM Y)‖ ≤ ‖g‖ * ‖quotientMkCLM Y‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 := mul_le_one₀ hg1 (norm_nonneg (quotientMkCLM Y)) (norm_quotientMkCLM_le Y)
      have h2 : ‖(‖xq‖)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ hpos
      exact mul_le_one₀ h2 (norm_nonneg _) h1
    · have hx : (g.comp (quotientMkCLM Y)) x = ‖xq‖ := by
        simpa [hxq] using hg2
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hx]
      field_simp
    · intro y hy
      have : (Submodule.Quotient.mk y : X ⧸ Y) = 0 := by
        rwa [Submodule.Quotient.mk_eq_zero]
      simp [this]
  · rintro ⟨f, hf1, hfx, hfY⟩
    have hne : ((Y : Set X)).Nonempty := ⟨0, Y.zero_mem⟩
    rw [ge_iff_le, Metric.le_infDist hne]
    intro y hy
    have h1 : f (x - y) = 1 := by
      rw [map_sub, hfx, hfY hy, sub_zero]
    have h2 : |f (x - y)| ≤ ‖f‖ * ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using f.le_opNorm (x - y)
    rw [h1] at h2
    have h3 : ‖f‖ * ‖x - y‖ ≤ ‖x - y‖ := by
      nlinarith [norm_nonneg (x - y), norm_nonneg f]
    rw [dist_eq_norm]
    simp only [abs_one] at h2
    linarith
