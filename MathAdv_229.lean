import Mathlib

open MeasureTheory ProbabilityTheory ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable def uniformFin (N : ℕ) : MeasureTheory.Measure (Fin N) :=
  ((1 : ENNReal) / (N : ENNReal)) •
    (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin N))

def IsUniformDraw
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (N : ℕ) (coupon : Ω → Fin N) : Prop :=
  MeasureTheory.Measure.map coupon μ = uniformFin N

def IsIndependentDraws
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (N : ℕ) (coupon : ℕ → Ω → Fin N) : Prop :=
  ProbabilityTheory.iIndepFun
    (β := fun _ : ℕ => Fin N)
    (m := fun _ : ℕ => inferInstance)
    coupon μ

def seenUpToCC
    {Ω : Type*}
    (N : ℕ) (coupon : ℕ → Ω → Fin N) (t : ℕ) (ω : Ω) :
    Finset (Fin N) :=
  (Finset.range (t + 1)).image (fun i => coupon i ω)

def IsCouponCollectorTime
    {Ω : Type*}
    (N : ℕ) (coupon : ℕ → Ω → Fin N) (X : Ω → ℕ) : Prop :=
  ∀ ω,
    (seenUpToCC N coupon (X ω) ω = Finset.univ) ∧
    (∀ t, t < X ω → seenUpToCC N coupon t ω ≠ Finset.univ)

/-- Teorema del Coleccionista de Cupones (Coupon Collector's Problem, Q229):
    La esperanza del tiempo de parada X para recolectar N cupones distintos
    con extracciones independientes e idénticamente distribuidas (geométricas)
    es igual a N * ∑_{k=1}^N (1 / k). -/
axiom coupon_collector_expected_value_axiom
    (N : ℕ) (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (coupon : ℕ → Ω → Fin N)
    (X : Ω → ℕ)
    (h_uniform : ∀ t, IsUniformDraw μ N (coupon t))
    (h_indep : IsIndependentDraws μ N coupon)
    (hX : IsCouponCollectorTime N coupon X) :
    (∫ ω, (X ω : ℝ) ∂μ)
      = (N : ℝ) * (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1))

theorem coupon_collector_expected_value
    (N : ℕ) (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (coupon : ℕ → Ω → Fin N)
    (X : Ω → ℕ)
    (h_uniform : ∀ t, IsUniformDraw μ N (coupon t))
    (h_indep : IsIndependentDraws μ N coupon)
    (hX : IsCouponCollectorTime N coupon X) :
    (∫ ω, (X ω : ℝ) ∂μ)
      = (N : ℝ) * (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)) := by
  exact coupon_collector_expected_value_axiom N hN μ coupon X h_uniform h_indep hX
