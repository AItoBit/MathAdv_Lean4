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

set_option grind.warning false

/-!
# Poisson summation for the Poisson kernel

For `t > 0` let `f x = t / (π (x² + t²))`.  With the Fourier transform normalised as
`f̂ ξ = ∫ f x e^{-2 π i x ξ} dx` one has `f̂ ξ = e^{-2 π t |ξ|}`, and the Poisson summation
formula `∑_{n ∈ ℤ} f n = ∑_{n ∈ ℤ} f̂ n` reads

`(1/π) ∑_{n ∈ ℤ} t / (t² + n²) = ∑_{n ∈ ℤ} e^{-2 π t |n|}`.

The theorem that yields the identity is (d), the **Poisson summation formula**.

This is `Stein17.stein_17` below.  Both sides equal `coth (π t) = (1 + q)/(1 - q)` with
`q = e^{-2 π t}`; we prove this directly, the analytic input being the Mittag-Leffler
expansion of the cotangent evaluated at the point `i t` of the upper half plane, together
with its `q`-expansion.

Note that the exponential factor really has to be `e^{-2 π t |n|}` and not `e^{-2 t |n|}`:
the version with `e^{-2 t |n|}` is false, see `Stein17.stein_17_without_pi_false` at the end
of the file.
-/

namespace Stein17

open Complex Real
open scoped UpperHalfPlane

/-- The quantity `q = e^{-2 π t}`, in terms of which both sides of the Poisson summation
identity have the closed form `(1 + q) / (1 - q)`. -/
noncomputable def q (t : ℝ) : ℝ := Real.exp (-(2 * π * t))

lemma q_pos (t : ℝ) : 0 < q t := Real.exp_pos _

lemma q_lt_one {t : ℝ} (ht : 0 < t) : q t < 1 := by
  have h : -(2 * π * t) < 0 := by nlinarith [Real.pi_pos]
  simpa [q] using Real.exp_lt_one_iff.mpr h

lemma one_sub_q_ne_zero {t : ℝ} (ht : 0 < t) : 1 - q t ≠ 0 :=
  sub_ne_zero.mpr (q_lt_one ht).ne'

/-! ### The right-hand side : a two-sided geometric series -/

/-- For `c > 0`, `∑_{n ∈ ℤ} e^{-c |n|} = (1 + e^{-c}) / (1 - e^{-c})`. -/
lemma tsum_int_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    ∑' (n : ℤ), Real.exp (-c * |(n : ℝ)|) =
      (1 + Real.exp (-c)) / (1 - Real.exp (-c)) := by
  have hq0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hne : 1 - Real.exp (-c) ≠ 0 := sub_ne_zero.mpr hq1.ne'
  set f : ℤ → ℝ := fun n => Real.exp (-c * |(n : ℝ)|) with hf
  have habs : ∀ m : ℤ, 0 ≤ m → f m = Real.exp (-c) ^ m.toNat := by
    intro m hm
    have h1 : |(m : ℝ)| = (m.toNat : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast hm)]
      exact_mod_cast (Int.toNat_of_nonneg hm).symm
    rw [hf]
    simp only [h1, ← Real.exp_nat_mul]
    ring_nf
  have heven : ∀ m : ℤ, f (-m) = f m := by
    intro m; simp [hf, abs_neg]
  have hgeo : HasSum (fun n : ℕ => Real.exp (-c) ^ (n + 1))
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (Real.exp (-c))
    have he : (fun i : ℕ => Real.exp (-c) * Real.exp (-c) ^ i)
        = fun n : ℕ => Real.exp (-c) ^ (n + 1) := by
      funext n; rw [pow_succ']
    rw [he] at h
    simpa [div_eq_mul_inv] using h
  have h1 : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have he : (fun n : ℕ => f ((n : ℤ) + 1)) = fun n : ℕ => Real.exp (-c) ^ (n + 1) := by
      funext n
      rw [habs _ (by positivity)]
      congr 1
    rw [he]; exact hgeo
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have he : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n : ℕ => f ((n : ℤ) + 1) := by
      funext n; exact heven _
    rw [he]; exact h1
  have h0 : f 0 = 1 := by simp [hf]
  have hs := h1.of_add_one_of_neg_add_one h2
  rw [hs.tsum_eq, h0]
  field_simp
  ring

lemma tsum_int_exp {t : ℝ} (ht : 0 < t) :
    ∑' (n : ℤ), Real.exp (-(2 * π * t) * |(n : ℝ)|) = (1 + q t) / (1 - q t) :=
  tsum_int_exp_neg_mul_abs (by positivity)

/-! ### The left-hand side : the Mittag-Leffler expansion of the cotangent at `i t` -/

lemma summable_shift (t : ℝ) :
    Summable fun n : ℕ => 1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hcomp : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hcomp
  have h1 : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have h2 : ((n : ℝ) + 1) ^ 2 ≤ t ^ 2 + ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg t]
  exact one_div_le_one_div_of_le h1 h2

/-- The real number `A t = ∑_{n ≥ 1} 1 / (t² + n²)`. -/
noncomputable def A (t : ℝ) : ℝ := ∑' n : ℕ, 1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)

/-- The terms of the Mittag-Leffler expansion of `π cot (π x)` at `x = i t` are purely
imaginary, and summing them gives `-2 i t · A t`. -/
lemma tsum_pnat_cot_terms {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x = (t : ℂ) * I) :
    ∑' (n : ℕ+), (1 / (x - ((n : ℕ) : ℂ)) + 1 / (x + ((n : ℕ) : ℂ))) =
      (-2 * (t : ℂ) * I) * ((A t : ℝ) : ℂ) := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / (x - (n : ℂ)) + 1 / (x + (n : ℂ)))]
  have hterm : ∀ n : ℕ, 1 / (x - ((n : ℕ) + 1 : ℕ)) + 1 / (x + ((n : ℕ) + 1 : ℕ)) =
      (-2 * (t : ℂ) * I) * ((1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    intro n
    have hden : (t : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2 ≠ 0 := by
      have h : ((t ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (0:ℝ) < t ^ 2 + ((n : ℝ) + 1) ^ 2).ne'
      push_cast at h
      exact h
    have hx1 : x - (((n : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := by
      rw [hx]
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    have hx2 : x + (((n : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := by
      rw [hx]
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    rw [hx] at hx1 hx2 ⊢
    push_cast at hx1 hx2 ⊢
    field_simp
    ring_nf
    simp
    ring
  rw [tsum_congr hterm, tsum_mul_left, ← Complex.ofReal_tsum]
  rfl

/-- The key closed form: `1/t + 2 t ∑_{n ≥ 1} 1/(t² + n²) = π (1 + q) / (1 - q)`, i.e.
`∑_{n ∈ ℤ} t/(t² + n²) = π coth (π t)`. -/
lemma key_identity {t : ℝ} (ht : 0 < t) :
    1 / t + 2 * t * A t = π * (1 + q t) / (1 - q t) := by
  have hq0 : 0 < q t := q_pos t
  have hq1 : q t < 1 := q_lt_one ht
  have hne : (1 : ℝ) - q t ≠ 0 := one_sub_q_ne_zero ht
  set z : ℍ := ⟨(t : ℂ) * I, by simp [ht]⟩ with hzdef
  have hzc : (z : ℂ) = (t : ℂ) * I := rfl
  have hmem : (z : ℂ) ∈ Complex.integerComplement := UpperHalfPlane.coe_mem_integerComplement z
  have hcot1 := cot_series_rep hmem
  have hcot2 := pi_mul_cot_pi_q_exp z
  have hQ : Complex.exp (2 * (π : ℂ) * I * (z : ℂ)) = ((q t : ℝ) : ℂ) := by
    rw [hzc, show (2 * (π : ℂ) * I * ((t : ℂ) * I)) = ((-(2 * π * t) : ℝ) : ℂ) by
      push_cast; ring_nf; simp [Complex.I_sq], ← Complex.ofReal_exp]
    rfl
  have hnormQ : ‖((q t : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hgeo : ∑' n : ℕ, ((q t : ℝ) : ℂ) ^ n = (1 - ((q t : ℝ) : ℂ))⁻¹ :=
    tsum_geometric_of_norm_lt_one hnormQ
  rw [hQ, hgeo] at hcot2
  rw [tsum_pnat_cot_terms ht hzc, hzc] at hcot1
  have E := hcot1.symm.trans hcot2
  have hL : (1 : ℂ) / ((t : ℂ) * I) + (-2 * (t : ℂ) * I) * ((A t : ℝ) : ℂ)
      = ((-(1 / t + 2 * t * A t) : ℝ) : ℂ) * I := by
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
    ring_nf
    simp
    ring
  have hR : (π : ℂ) * I - 2 * (π : ℂ) * I * (1 - ((q t : ℝ) : ℂ))⁻¹
      = ((π - 2 * π / (1 - q t) : ℝ) : ℂ) * I := by
    have h1 : ((1 : ℂ) - ((q t : ℝ) : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hne)
    push_cast
    field_simp
  rw [hL, hR] at E
  have E2 := mul_right_cancel₀ Complex.I_ne_zero E
  have E3 : -(1 / t + 2 * t * A t) = π - 2 * π / (1 - q t) := by exact_mod_cast E2
  field_simp at E3 ⊢
  linarith [E3]

lemma tsum_int_cauchy {t : ℝ} (ht : 0 < t) :
    ∑' (n : ℤ), t / (t ^ 2 + (n : ℝ) ^ 2) = π * (1 + q t) / (1 - q t) := by
  set f : ℤ → ℝ := fun n => t / (t ^ 2 + (n : ℝ) ^ 2) with hf
  have hshift : (fun n : ℕ => f ((n : ℤ) + 1))
      = fun n : ℕ => t * (1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
    funext n; simp [hf]; ring
  have hshift' : (fun n : ℕ => f (-((n : ℤ) + 1)))
      = fun n : ℕ => t * (1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
    funext n; simp [hf]; ring
  have hS : Summable fun n : ℕ => t * (1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2)) :=
    (summable_shift t).mul_left t
  have h1 : Summable fun n : ℕ => f ((n : ℤ) + 1) := by rw [hshift]; exact hS
  have h2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) := by rw [hshift']; exact hS
  rw [tsum_of_add_one_of_neg_add_one h1 h2, hshift, hshift', tsum_mul_left]
  have h0 : f 0 = 1 / t := by simp [hf, sq]
  rw [h0]
  have hA : A t = ∑' n : ℕ, 1 / (t ^ 2 + ((n : ℝ) + 1) ^ 2) := rfl
  rw [← hA]
  linarith [key_identity ht]

/-! ### The Poisson summation identity -/

/-- **Poisson summation for the Poisson kernel.**  For `t > 0`,
`(1/π) ∑_{n ∈ ℤ} t / (t² + n²) = ∑_{n ∈ ℤ} e^{-2 π t |n|}`.

This is the identity obtained by applying the Poisson summation formula to
`f x = t / (π (x² + t²))`, whose Fourier transform (with the convention
`f̂ ξ = ∫ f x e^{-2 π i x ξ} dx`) is `f̂ ξ = e^{-2 π t |ξ|}`.  Both sides are equal to
`coth (π t)`. -/
theorem stein_17 {t : ℝ} (ht : 0 < t) :
    (1 / Real.pi) * ∑' (n : ℤ), t / (t ^ 2 + (n : ℝ) ^ 2) =
      ∑' (n : ℤ), Real.exp (-(2 * π * t) * |(n : ℝ)|) := by
  rw [tsum_int_cauchy ht, tsum_int_exp ht]
  field_simp

/-! ### The version without the factor `π` in the exponent is false

The statement as originally posed,



is not correct: with the standard normalisation of the Fourier transform the transform of
`x ↦ t / (π (x² + t²))` is `ξ ↦ e^{-2 π t |ξ|}`, not `ξ ↦ e^{-2 t |ξ|}`.  Indeed the left-hand
side equals `coth (π t)` while the right-hand side equals `coth t`.  We record this below.
-/

/-- The identity with `e^{-2 t |n|}` in place of `e^{-2 π t |n|}` fails (already at `t = 1`);
the two sides are `coth (π t)` and `coth t`. -/
theorem stein_17_without_pi_false :
    ¬ ∀ t : ℝ, 0 < t → (1 / Real.pi) * ∑' (n : ℤ), t / (t ^ 2 + (n : ℝ) ^ 2) =
      ∑' (n : ℤ), Real.exp (-2 * t * |(n : ℝ)|) := by
  intro h
  have h1 := h 1 one_pos
  rw [tsum_int_cauchy one_pos] at h1
  have h2 : ∑' (n : ℤ), Real.exp (-2 * (1 : ℝ) * |(n : ℝ)|)
      = (1 + Real.exp (-2)) / (1 - Real.exp (-2)) := by
    have := tsum_int_exp_neg_mul_abs (c := 2) two_pos
    simpa using this
  rw [h2] at h1
  set a : ℝ := q 1 with ha
  set b : ℝ := Real.exp (-2) with hb
  have hb0 : 0 < b := Real.exp_pos _
  have hb1 : b < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have ha0 : 0 < a := q_pos 1
  have hab : a < b := by
    rw [ha, hb, q]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_gt_three])
  have hane : (1 : ℝ) - a ≠ 0 := one_sub_q_ne_zero one_pos
  have hlt : (1 + a) / (1 - a) < (1 + b) / (1 - b) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hpi : (0:ℝ) < π := Real.pi_pos
  have h3 : (1 + a) / (1 - a) = (1 + b) / (1 - b) := by
    field_simp at h1
    field_simp
    nlinarith [h1]
  exact absurd h3 hlt.ne

end Stein17
