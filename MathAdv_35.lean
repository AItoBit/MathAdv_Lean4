import Mathlib

/-!
# ∫ (∛x + 10⁵√(x³)) dx = (3/4)x^(4/3) + (25/4)x^(8/5) + C

The original statement

```
theorem dawkins_5_2_6 (C : ℝ) :
  ∫ x, x^(1/3) + 10 * x^(3/5) = (3/4) * x^(4/3) + (25/4) * x^(8/5) + C
```

is not a faithful formalization: the exponents `1/3`, `3/5`, ... are natural-number
divisions (all equal to `0` or `1`), the variable `x` on the right-hand side is free,
and an indefinite integral is not expressible as `∫ x, f x` (which is the integral
over all of `ℝ`).  We therefore formalize the statement in the two standard ways:

* `dawkins_5_2_6_hasDerivAt` : the proposed antiderivative really has the integrand
  as its derivative (this is exactly the meaning of the indefinite integral formula);
* `dawkins_5_2_6_intervalIntegral` : the corresponding fundamental-theorem-of-calculus
  statement on an interval `[a, b]` with `0 < a`.

Real powers are `Real.rpow`, and the statements are given for `x > 0`, where
`∛x = x^(1/3)` and `⁵√(x³) = x^(3/5)` are differentiable.
-/

open Real

/-- The integrand `∛x + 10 · ⁵√(x³) = x^(1/3) + 10 * x^(3/5)`. -/
noncomputable def dawkinsIntegrand (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 3) + 10 * x ^ ((3 : ℝ) / 5)

/-- The proposed antiderivative `(3/4)·x^(4/3) + (25/4)·x^(8/5) + C`. -/
noncomputable def dawkinsAntideriv (C x : ℝ) : ℝ :=
  (3 / 4) * x ^ ((4 : ℝ) / 3) + (25 / 4) * x ^ ((8 : ℝ) / 5) + C

/-- For every `x > 0` and every constant `C`, the function
`x ↦ (3/4)x^(4/3) + (25/4)x^(8/5) + C` has derivative `x^(1/3) + 10x^(3/5)` at `x`. -/
theorem dawkins_5_2_6_hasDerivAt (C : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dawkinsAntideriv C) (dawkinsIntegrand x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ ((4 : ℝ) / 3))
      ((4 / 3) * x ^ ((4 : ℝ) / 3 - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ ((8 : ℝ) / 5))
      ((8 / 5) * x ^ ((8 : ℝ) / 5 - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have key : (3 : ℝ) / 4 * (4 / 3 * x ^ ((4 : ℝ) / 3 - 1))
      + 25 / 4 * (8 / 5 * x ^ ((8 : ℝ) / 5 - 1)) = dawkinsIntegrand x := by
    rw [show (4 : ℝ) / 3 - 1 = 1 / 3 by norm_num, show (8 : ℝ) / 5 - 1 = 3 / 5 by norm_num]
    unfold dawkinsIntegrand
    ring
  have h : HasDerivAt (dawkinsAntideriv C)
      ((3 : ℝ) / 4 * (4 / 3 * x ^ ((4 : ℝ) / 3 - 1))
        + 25 / 4 * (8 / 5 * x ^ ((8 : ℝ) / 5 - 1))) x :=
    ((h1.const_mul (3 / 4 : ℝ)).add (h2.const_mul (25 / 4 : ℝ))).add_const C
  rwa [key] at h

/-- Fundamental theorem of calculus form: for `0 < a` and `a ≤ b`,
`∫ x in a..b, (x^(1/3) + 10 x^(3/5)) = F b - F a` where
`F x = (3/4)x^(4/3) + (25/4)x^(8/5) + C`. -/
theorem dawkins_5_2_6_intervalIntegral (C : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, dawkinsIntegrand x) = dawkinsAntideriv C b - dawkinsAntideriv C a := by
  have hpos : ∀ y ∈ Set.uIcc a b, 0 < y := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le (lt_of_lt_of_le ha hab) h.1
  have hcont : ContinuousOn dawkinsIntegrand (Set.uIcc a b) := by
    apply ContinuousOn.add
    · exact ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (hpos y hy).ne'
    · exact ContinuousOn.const_smul
        (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (hpos y hy).ne') (10 : ℝ)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => dawkins_5_2_6_hasDerivAt C (hpos y hy)) hcont.intervalIntegrable

/-
Answer to the accompanying multiple-choice question: (a) the Power Rule for Integration,
i.e. `∫ xⁿ dx = x^(n+1)/(n+1) + C`, applied with `n = 1/3` and `n = 3/5`, which is exactly
what the derivative computation above verifies.
-/

#print axioms dawkins_5_2_6_hasDerivAt
#print axioms dawkins_5_2_6_intervalIntegral
