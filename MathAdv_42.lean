import Mathlib

/-!
# A reduction formula for `∫ xⁿ⁺¹ / (x² + 1) dx`

The informal statement is

  `∫ x^(n+1)/(x²+1) dx = x^n / n - ∫ x^(n-1)/(x²+1) dx`   (for `n ≠ 0`),

an identity between indefinite integrals (i.e. up to a constant of integration).
The tool needed is just the *power rule*: the algebraic simplification

  `x^(n+1)/(x²+1) = x^(n-1) - x^(n-1)/(x²+1)`

reduces the problem to `∫ x^(n-1) dx = x^n / n`.

We formalise the identity in the mathematically precise form of definite
(interval) integrals, where "up to a constant" becomes the difference
`bⁿ/n - aⁿ/n` of the antiderivative at the endpoints.

The originally supplied statement

```
theorem strang_7_3_33 (C : ℝ) {n : ℕ} (hn : n ≠ 0) :
  (∫ x, x^(n+1) / (x^2 + 1)) = x^n / n - (∫ x, x^(n-1) / (x^2 + 1)) + C
```

is not a faithful formalisation: `∫ x, f x` denotes the Lebesgue integral over
all of `ℝ` (a number, in fact `0` here since the integrands are not integrable),
while `x` occurs free on the right-hand side.  It is therefore replaced by the
interval-integral version below.
-/

/-- The pointwise algebraic identity behind the reduction formula:
`x^(n+1)/(x²+1) = x^(n-1) - x^(n-1)/(x²+1)` for `n ≥ 1`. -/
theorem pow_div_sq_add_one_eq (n : ℕ) (hn : n ≠ 0) (x : ℝ) :
    x ^ (n + 1) / (x ^ 2 + 1) = x ^ (n - 1) - x ^ (n - 1) / (x ^ 2 + 1) := by
  have hx : (0 : ℝ) < x ^ 2 + 1 := by positivity
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- **Reduction formula.**  For `n ≠ 0` and all real `a, b`,
`∫ x in a..b, x^(n+1)/(x²+1) = (bⁿ - aⁿ)/n - ∫ x in a..b, x^(n-1)/(x²+1)`,
i.e. `∫ x^(n+1)/(x²+1) dx = xⁿ/n - ∫ x^(n-1)/(x²+1) dx` up to a constant. -/
theorem integral_pow_div_sq_add_one (n : ℕ) (hn : n ≠ 0) (a b : ℝ) :
    (∫ x in a..b, x ^ (n + 1) / (x ^ 2 + 1))
      = (b ^ n - a ^ n) / n - ∫ x in a..b, x ^ (n - 1) / (x ^ 2 + 1) := by
  have hcont : Continuous fun x : ℝ => x ^ (n - 1) / (x ^ 2 + 1) := by
    apply Continuous.div (by continuity) (by continuity)
    intro x; positivity
  have hint₁ : IntervalIntegrable (fun x : ℝ => x ^ (n - 1)) MeasureTheory.volume a b :=
    (continuous_pow _).intervalIntegrable a b
  have hint₂ : IntervalIntegrable (fun x : ℝ => x ^ (n - 1) / (x ^ 2 + 1))
      MeasureTheory.volume a b := hcont.intervalIntegrable a b
  have hpow : (∫ x in a..b, x ^ (n - 1)) = (b ^ n - a ^ n) / n := by
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [integral_pow, show n - 1 + 1 = n by omega,
      show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by
        rw [Nat.cast_sub h1]; push_cast; ring]
  calc (∫ x in a..b, x ^ (n + 1) / (x ^ 2 + 1))
      = ∫ x in a..b, (x ^ (n - 1) - x ^ (n - 1) / (x ^ 2 + 1)) := by
        exact intervalIntegral.integral_congr
          (fun x _ => pow_div_sq_add_one_eq n hn x)
    _ = (∫ x in a..b, x ^ (n - 1)) - ∫ x in a..b, x ^ (n - 1) / (x ^ 2 + 1) :=
        intervalIntegral.integral_sub hint₁ hint₂
    _ = (b ^ n - a ^ n) / n - ∫ x in a..b, x ^ (n - 1) / (x ^ 2 + 1) := by rw [hpow]
