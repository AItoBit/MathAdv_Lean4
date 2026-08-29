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

/-!
# The polynomial `z^6 + 4z^2 - 1` has exactly two zeros in the open unit disc

The classical argument uses Rouché's theorem: on `|z| = 1` one has
`|z^6 - 1| ≤ 2 < 4 = |4z^2|`, so `z^6 + 4z^2 - 1` has the same number of zeros
(counted with multiplicity) inside the unit circle as `4z^2`, namely two.

The proof below is an explicit, self-contained version of the same count.
Substituting `w = z^2` turns the polynomial into the cubic `w^3 + 4w - 1`,
which has a unique root `r` in `(0, 1)` (obtained from the intermediate value
theorem).  Factoring

`z^6 + 4z^2 - 1 = (z^2 - r) * (z^4 + r z^2 + (r^2 + 4))`  (valid since `r^3 + 4r = 1`),

the first factor contributes the two real zeros `± √r`, both of modulus `√r < 1`,
while any root of the second factor satisfies `‖z^2‖ ≥ 1` and hence lies outside
the open unit disc.
-/

/-- The cubic `x ^ 3 + 4 * x - 1` has a root in the open interval `(0, 1)`. -/
theorem exists_cubic_root_mem_Ioo :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ^ 3 + 4 * r = 1 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + 4 * x) (Set.Icc 0 1) := by fun_prop
  have h := intermediate_value_Ioo (le_of_lt (zero_lt_one (α := ℝ))) hc
  have hmem : (1 : ℝ) ∈ Set.Ioo ((0 : ℝ) ^ 3 + 4 * 0) ((1 : ℝ) ^ 3 + 4 * 1) := by norm_num
  obtain ⟨r, hr, hfr⟩ := h hmem
  exact ⟨r, hr.1, hr.2, hfr⟩

/-- Given a root `r ∈ (0,1)` of the cubic `x^3 + 4x - 1`, the zero set of
`z^6 + 4z^2 - 1` inside the open unit disc is exactly `{√r, -√r}`, a set of
cardinality `2`. -/
theorem card_zeros_of_cubic_root (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 3 + 4 * r = 1) :
    Nat.card { z : ℂ | ‖z‖ < 1 ∧ z ^ 6 + 4 * z ^ 2 - 1 = 0 } = 2 := by
  obtain ⟨s, hs0, hs1, hsq⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ s ^ 2 = r := by
    refine ⟨Real.sqrt r, Real.sqrt_pos.mpr hr0, ?_, Real.sq_sqrt hr0.le⟩
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hr0.le hr1
  have hrC : (r : ℂ) ^ 3 + 4 * (r : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hr
  have hsqC : ((s : ℂ)) ^ 2 = (r : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hsq
  have hnorms : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have hroot : ((s : ℂ)) ^ 6 + 4 * (s : ℂ) ^ 2 - 1 = 0 := by
    linear_combination ((s : ℂ) ^ 4 + (s : ℂ) ^ 2 * (r : ℂ) + (r : ℂ) ^ 2 + 4) * hsqC + hrC
  have hset : { z : ℂ | ‖z‖ < 1 ∧ z ^ 6 + 4 * z ^ 2 - 1 = 0 } = {(s : ℂ), -(s : ℂ)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, heq⟩
      have hfac : (z ^ 2 - (r : ℂ)) * (z ^ 4 + (r : ℂ) * z ^ 2 + ((r : ℂ) ^ 2 + 4)) = 0 := by
        linear_combination heq - hrC
      rcases mul_eq_zero.mp hfac with h | h
      · -- the factor `z ^ 2 - r`, giving the two zeros `± s`
        have h2 : (z - (s : ℂ)) * (z + (s : ℂ)) = 0 := by linear_combination h - hsqC
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact Or.inl (sub_eq_zero.mp h3)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
      · -- the quartic factor has no root in the closed unit disc
        exfalso
        have hnu : ‖z ^ 2‖ < 1 := by
          rw [norm_pow]; nlinarith [norm_nonneg z]
        have key : (z ^ 2) ^ 2 + (r : ℂ) * z ^ 2 = -((r : ℂ) ^ 2 + 4) := by linear_combination h
        have h1 : ‖(z ^ 2) ^ 2 + (r : ℂ) * z ^ 2‖ ≤ ‖z ^ 2‖ ^ 2 + r * ‖z ^ 2‖ := by
          calc ‖(z ^ 2) ^ 2 + (r : ℂ) * z ^ 2‖ ≤ ‖(z ^ 2) ^ 2‖ + ‖(r : ℂ) * z ^ 2‖ :=
                norm_add_le _ _
            _ = ‖z ^ 2‖ ^ 2 + r * ‖z ^ 2‖ := by
                rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        have h2 : ‖(-((r : ℂ) ^ 2 + 4))‖ = r ^ 2 + 4 := by
          rw [norm_neg, show ((r : ℂ) ^ 2 + 4) = ((r ^ 2 + 4 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith)]
        rw [key, h2] at h1
        nlinarith [norm_nonneg (z ^ 2)]
    · rintro (rfl | rfl)
      · exact ⟨by rw [hnorms]; exact hs1, hroot⟩
      · exact ⟨by rw [norm_neg, hnorms]; exact hs1, by linear_combination hroot⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair]
  intro hcon
  have h2s : (2 : ℂ) * (s : ℂ) = 0 := by linear_combination hcon
  have hs' : (s : ℝ) = 0 := by
    rcases mul_eq_zero.mp h2s with h | h
    · norm_num at h
    · exact_mod_cast h
  exact absurd hs' hs0.ne'

/-- **The polynomial `z^6 + 4z^2 - 1` has exactly two zeros inside the circle `|z| = 1`.** -/
theorem question_5 :
    Nat.card { z : ℂ | ‖z‖ < 1 ∧ z ^ 6 + 4 * z ^ 2 - 1 = 0 } = 2 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_cubic_root_mem_Ioo
  exact card_zeros_of_cubic_root r hr0 hr1 hr
