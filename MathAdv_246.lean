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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace RequestProject

open MeasureTheory ProbabilityTheory

/-- Cross-moment identity: for a martingale, `E[X 0 * X n] = E[X 0 * X 0]`.
This is the "tower rule" step: conditioning on `ℱ 0` and pulling out the
`ℱ 0`-measurable factor `X 0`. -/
theorem integral_mul_zero_eq_of_martingale
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : Martingale X ℱ μ)
    (h_L2 : ∀ n, MemLp (X n) (2 : ENNReal) μ)
    (n : ℕ) :
    ∫ ω, X 0 ω * X n ω ∂μ = ∫ ω, X 0 ω * X 0 ω ∂μ := by
  have hm0 : ℱ 0 ≤ m := ℱ.le 0
  have hX0 : StronglyMeasurable[ℱ 0] (X 0) := h_mart.1 0
  have hint_n : Integrable (X n) μ := h_mart.integrable n
  have hprod : Integrable (X 0 * X n) μ := (h_L2 0).integrable_mul (h_L2 n)
  have hcond : μ[X 0 * X n | ℱ 0] =ᵐ[μ] X 0 * X 0 := by
    refine (condExp_mul_of_stronglyMeasurable_left hX0 hprod hint_n).trans ?_
    filter_upwards [h_mart.condExp_ae_eq (Nat.zero_le n)] with ω hω
    simp [Pi.mul_apply, hω]
  calc ∫ ω, X 0 ω * X n ω ∂μ = ∫ ω, (X 0 * X n) ω ∂μ := rfl
    _ = ∫ ω, μ[X 0 * X n | ℱ 0] ω ∂μ := (integral_condExp hm0).symm
    _ = ∫ ω, (X 0 * X 0) ω ∂μ := integral_congr_ae hcond
    _ = ∫ ω, X 0 ω * X 0 ω ∂μ := rfl

/-- Second moments agree: if `X n` and `X 0` are identically distributed then
`E[(X n)^2] = E[(X 0)^2]`. -/
theorem integral_sq_eq_of_identDistrib
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω}
    (X : ℕ → Ω → ℝ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (n : ℕ) :
    ∫ ω, X n ω ^ 2 ∂μ = ∫ ω, X 0 ω ^ 2 ∂μ :=
  ((h_ident n).comp (measurable_id.pow_const 2)).integral_eq

/-- The `L²` distance between `X n` and `X 0` vanishes. -/
theorem integral_sub_sq_eq_zero
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : Martingale X ℱ μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h_L2 : ∀ n, MemLp (X n) (2 : ENNReal) μ)
    (n : ℕ) :
    ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ = 0 := by
  have hsqn : Integrable (fun ω => X n ω ^ 2) μ := (h_L2 n).integrable_sq
  have hsq0 : Integrable (fun ω => X 0 ω ^ 2) μ := (h_L2 0).integrable_sq
  have hprod : Integrable (fun ω => X 0 ω * X n ω) μ := (h_L2 0).integrable_mul (h_L2 n)
  have hexp : ∀ ω, (X n ω - X 0 ω) ^ 2
      = X n ω ^ 2 + (X 0 ω ^ 2 - 2 * (X 0 ω * X n ω)) := by
    intro ω; ring
  have h1 : ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ
      = (∫ ω, X n ω ^ 2 ∂μ) + ((∫ ω, X 0 ω ^ 2 ∂μ) - 2 * ∫ ω, X 0 ω * X n ω ∂μ) := by
    have hcm : Integrable (fun ω => 2 * (X 0 ω * X n ω)) μ := hprod.const_mul 2
    have h2 : Integrable (fun ω => X 0 ω ^ 2 - 2 * (X 0 ω * X n ω)) μ := hsq0.sub hcm
    simp_rw [hexp]
    rw [integral_add hsqn h2, integral_sub hsq0 hcm, integral_const_mul]
  rw [h1, integral_mul_zero_eq_of_martingale X h_mart h_L2 n,
    integral_sq_eq_of_identDistrib X h_ident n]
  have : ∀ ω, X 0 ω * X 0 ω = X 0 ω ^ 2 := by intro ω; ring
  simp_rw [this]
  ring

/-!
The statement as originally posed uses `MeasureTheory.Memℒp`, which no longer exists in the
current Mathlib (it was renamed to `MeasureTheory.MemLp`).  The original statement is kept
below, commented out, and the theorem is restated with `MemLp`, which has exactly the same
meaning (finiteness of the second moment).

```
theorem problem_19
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : MeasureTheory.Martingale X ℱ μ)
    (h_ident : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (h_finite_mom : ∀ n, MeasureTheory.Memℒp (X n) (2 : ENNReal) μ) :
    ∀ n, X n =ᵐ[μ] X 0
```
-/

/-- If `X` is a martingale whose marginals all have the same (square-integrable)
distribution, then `X n = X 0` almost surely for every `n`. -/
theorem problem_19
    {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (h_mart : MeasureTheory.Martingale X ℱ μ)
    (h_ident : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (h_finite_mom : ∀ n, MeasureTheory.MemLp (X n) (2 : ENNReal) μ) :
    ∀ n, X n =ᵐ[μ] X 0 := by
  intro n
  have hzero : ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ = 0 :=
    integral_sub_sq_eq_zero X h_mart h_ident h_finite_mom n
  have hint : Integrable (fun ω => (X n ω - X 0 ω) ^ 2) μ :=
    ((h_finite_mom n).sub (h_finite_mom 0)).integrable_sq
  have hnonneg : 0 ≤ᵐ[μ] fun ω => (X n ω - X 0 ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hae] with ω hω
  have hsq : (X n ω - X 0 ω) ^ 2 = 0 := hω
  have h0 : X n ω - X 0 ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linarith

end RequestProject
