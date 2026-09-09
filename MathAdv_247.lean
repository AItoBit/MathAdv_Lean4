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
set_option pp.piBinderTypes true

set_option grind.warning false

/-- If `X ≤ 1` almost surely (here: `P(X > 1) = 0`) and `θ ≥ 0`, then
`log M(θ) ≤ θ`, where `M(θ) = E[exp(θ X)]`. -/
lemma log_mgf_le_of_le_one
  {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (X : Ω → ℝ) (h_bounded : P {ω | X ω > 1} = 0)
  {θ : ℝ} (hθ : 0 ≤ θ) :
  Real.log (∫ ω, Real.exp (θ * X ω) ∂P) ≤ θ := by
  have hae : ∀ᵐ ω ∂P, X ω ≤ 1 := by
    have h := (MeasureTheory.measure_eq_zero_iff_ae_notMem
      (μ := P) (s := {ω | X ω > 1})).mp h_bounded
    filter_upwards [h] with ω hω
    simpa using hω
  by_cases hint : MeasureTheory.Integrable (fun ω => Real.exp (θ * X ω)) P
  · have h1 : (∫ ω, Real.exp (θ * X ω) ∂P) ≤ Real.exp θ := by
      have h2 : (∫ ω, Real.exp (θ * X ω) ∂P) ≤ ∫ _ω, Real.exp θ ∂P := by
        apply MeasureTheory.integral_mono_ae hint (MeasureTheory.integrable_const _)
        filter_upwards [hae] with ω hω
        exact Real.exp_le_exp.mpr (by nlinarith)
      simpa using h2
    rcases le_or_gt (∫ ω, Real.exp (θ * X ω) ∂P) 0 with h0 | h0
    · have h2 : (∫ ω, Real.exp (θ * X ω) ∂P) = 0 := le_antisymm h0
        (MeasureTheory.integral_nonneg (fun ω => (Real.exp_pos _).le))
      simp [h2, hθ]
    · calc Real.log (∫ ω, Real.exp (θ * X ω) ∂P) ≤ Real.log (Real.exp θ) :=
            Real.log_le_log h0 h1
        _ = θ := Real.log_exp θ
  · simp [MeasureTheory.integral_undef hint, hθ]

/-- If `P(X > 1) = 0` and `P(X > 1 - ε) > 0` for every `ε > 0`, then the large deviations
rate function `I(x) = sup_θ (θ x - log M(θ))` is `+∞` for every `x > 1`.
(The support hypothesis `h_support` is not needed for this direction.) -/
theorem problem_20
  {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (X : Ω → ℝ)
  (h_bounded : P {ω | X ω > 1} = 0)
  (h_support : ∀ ε > 0, P {ω | X ω > 1 - ε} > 0) :
  let M := fun (θ : ℝ) => ∫ ω, Real.exp (θ * X ω) ∂P
  let I := fun (x : ℝ) => ⨆ θ : ℝ, ((θ * x - Real.log (M θ)) : EReal)
  ∀ x > 1, I x = ⊤ := by
  intro M I x hx
  simp only [I, M]
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨r, hr⟩ : ∃ r : ℝ, b < (r : EReal) := by
    induction b with
    | bot => exact ⟨0, by simp⟩
    | coe q => exact ⟨q + 1, by exact_mod_cast by norm_num⟩
    | top => exact absurd hb (lt_irrefl _)
  refine ⟨(|r| + 1) / (x - 1), lt_of_lt_of_le hr ?_⟩
  set θ : ℝ := (|r| + 1) / (x - 1) with hθdef
  have hx1 : (0:ℝ) < x - 1 := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by positivity) hx1.le
  have hlog := log_mgf_le_of_le_one X h_bounded hθ0
  have key : r ≤ θ * x - Real.log (∫ ω, Real.exp (θ * X ω) ∂P) := by
    have hmul : θ * (x - 1) = |r| + 1 := div_mul_cancel₀ _ (ne_of_gt hx1)
    have habs : r ≤ |r| := le_abs_self r
    nlinarith [hlog, habs, hmul]
  calc (r : EReal) ≤ ((θ * x - Real.log (∫ ω, Real.exp (θ * X ω) ∂P) : ℝ) : EReal) := by
        exact_mod_cast key
    _ = (θ : EReal) * (x : EReal) - ((Real.log (∫ ω, Real.exp (θ * X ω) ∂P) : ℝ) : EReal) := by
        rw [EReal.coe_sub, EReal.coe_mul]

