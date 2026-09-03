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

/-- `phi` is an orthogonal family of functions on the interval from `a` to `b`. -/
def orthogonalOn (phi : ℕ → ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ {m n : ℕ}, m ≠ n →
    ∫ x in a..b, phi m x * phi n x = 0

/-- The elementary antiderivative computation
`∫₀^c sin (a r) sin (b r) dr = (sin ((a-b)c)/(a-b) - sin ((a+b)c)/(a+b))/2`. -/
theorem integral_sin_mul_sin_eq (a b c : ℝ) (hd : a - b ≠ 0) (hs : a + b ≠ 0) :
    (∫ r in (0:ℝ)..c, Real.sin (a * r) * Real.sin (b * r))
      = (Real.sin ((a - b) * c) / (a - b) - Real.sin ((a + b) * c) / (a + b)) / 2 := by
  have key : ∀ x ∈ Set.uIcc (0:ℝ) c,
      HasDerivAt (fun r : ℝ =>
          (Real.sin ((a - b) * r) / (a - b) - Real.sin ((a + b) * r) / (a + b)) / 2)
        (Real.sin (a * x) * Real.sin (b * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => Real.sin ((a - b) * r))
        (Real.cos ((a - b) * x) * (a - b)) x := by
      simpa using (((hasDerivAt_id x).const_mul (a - b)).sin)
    have h2 : HasDerivAt (fun r : ℝ => Real.sin ((a + b) * r))
        (Real.cos ((a + b) * x) * (a + b)) x := by
      simpa using (((hasDerivAt_id x).const_mul (a + b)).sin)
    have h := ((h1.div_const (a - b)).sub (h2.div_const (a + b))).div_const 2
    refine h.congr_deriv ?_
    have e1 : (a - b) * x = a * x - b * x := by ring
    have e2 : (a + b) * x = a * x + b * x := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  have hcont : IntervalIntegrable (fun r : ℝ => Real.sin (a * r) * Real.sin (b * r))
      MeasureTheory.volume 0 c :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))).intervalIntegrable 0 c
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt key hcont
  simpa using this

/-- A root of the mixed equation satisfies `sin (α c) = α c * cos (α c)`, and `cos (α c) ≠ 0`. -/
theorem sin_eq_of_tan_eq {t : ℝ} (h : Real.tan t = t) :
    Real.cos t ≠ 0 ∧ Real.sin t = t * Real.cos t := by
  have hcos : Real.cos t ≠ 0 := by
    intro hc
    have h0 : t = 0 := by
      rw [Real.tan_eq_sin_div_cos, hc, div_zero] at h; exact h.symm
    subst h0
    revert hc
    norm_num
  refine ⟨hcos, ?_⟩
  have := h
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hcos] at this
  exact this

/-- Orthogonality of the eigenfunctions for the insulated sphere. -/
theorem brown_6
    (c : ℝ)
    (_hc : 0 < c)
    (α : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ α n)
    (hinj : Function.Injective α)
    (hα : ∀ n, Real.tan (α n * c) = α n * c) :
    orthogonalOn (fun n r => Real.sin (α n * r)) 0 c := by
  intro m n hmn
  have hab : α m ≠ α n := fun h => hmn (hinj h)
  have hd : α m - α n ≠ 0 := sub_ne_zero.mpr hab
  have hsum : α m + α n ≠ 0 := by
    intro h
    have hm : α m = 0 := le_antisymm (by linarith [hpos n]) (hpos m)
    have hn : α n = 0 := le_antisymm (by linarith [hpos m]) (hpos n)
    exact hab (hm.trans hn.symm)
  obtain ⟨_, hsa⟩ := sin_eq_of_tan_eq (hα m)
  obtain ⟨_, hsb⟩ := sin_eq_of_tan_eq (hα n)
  simp only []
  rw [integral_sin_mul_sin_eq (α m) (α n) c hd hsum]
  have e1 : (α m - α n) * c = α m * c - α n * c := by ring
  have e2 : (α m + α n) * c = α m * c + α n * c := by ring
  rw [e1, e2, Real.sin_sub, Real.sin_add, hsa, hsb]
  field_simp
  ring
