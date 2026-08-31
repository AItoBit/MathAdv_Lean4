import Mathlib

/-!
# Gauss–Bonnet consequence: a metric on `S²` with curvature `≤ 1` has volume `≥ 4π`

This file contains a measure-theoretic core of the following geometric statement:

> If `g` is a metric on the sphere `S²` with Gauss curvature `K ≤ 1`, then
> `vol(S², g) ≥ 4π`.

By the Gauss–Bonnet theorem, `∫ K dvol = 2π · χ(S²) = 4π`.  Since `K ≤ 1` pointwise,
`4π = ∫ K dvol ≤ ∫ 1 dvol = vol(S², g)`.

The statement below abstracts this argument: `μ` is the (finite) volume measure, `K` the
curvature function, `h_total` is the conclusion of Gauss–Bonnet, and the conclusion is the
desired volume bound.
-/

/-- Measure-theoretic core of "a metric on `S²` with curvature `≤ 1` has volume `≥ 4π`":
if the total integral of `K` is `4π` (Gauss–Bonnet) and `K ≤ 1` almost everywhere, then the
total measure is at least `4π`.

The hypothesis `hK_meas` is part of the requested statement but is not needed for the proof
(it follows from `hK_int`). -/
theorem Petersen_4_6_core
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (hμ_fin : μ Set.univ ≠ (⊤ : ENNReal))
    (K : α → ℝ)
    (_hK_meas : MeasureTheory.AEStronglyMeasurable K μ)
    (hK_int : MeasureTheory.Integrable K μ)
    (hK_le : ∀ᵐ x ∂μ, K x ≤ 1)
    (h_total : (∫ x, K x ∂μ) = 4 * Real.pi) :
    4 * Real.pi ≤ (μ Set.univ).toReal := by
  have : MeasureTheory.IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμ_fin⟩
  have hconst : MeasureTheory.Integrable (fun _ : α => (1 : ℝ)) μ :=
    MeasureTheory.integrable_const 1
  have hmono : (∫ x, K x ∂μ) ≤ ∫ _x, (1 : ℝ) ∂μ :=
    MeasureTheory.integral_mono_ae hK_int hconst hK_le
  rw [h_total, MeasureTheory.integral_const, smul_eq_mul, mul_one] at hmono
  exact hmono
