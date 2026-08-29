import Mathlib

/-!
# Uniform convergence of `∑_{j=1}^n (1/z)^j` on `{z : ℂ | 5 ≤ ‖z‖}`

The partial sums of the geometric series `∑_{j ≥ 1} (1/z)^j` converge uniformly on the
set `{z : ℂ | 5 ≤ ‖z‖}`.  The proof is by the **Weierstrass M-test**: on that set
`‖(1/z)^j‖ ≤ (1/5)^j`, and `∑_j (1/5)^j` is a convergent geometric series.
-/

open Filter Topology

namespace UniformGeometric

/-- The terms of the series, with the `j = 0` term set to `0`, so that summing over
`Finset.range (n+1)` reproduces `∑_{j = 1}^{n}`. -/
noncomputable def term (j : ℕ) (z : ℂ) : ℂ := if j = 0 then 0 else (1 / z) ^ j

lemma sum_range_succ_term (n : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range (n + 1), term j z = ∑ j ∈ Finset.Icc 1 n, (1 / z) ^ j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  simp only [term, if_true, zero_add, Nat.succ_eq_add_one]
  rw [Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  rw [if_neg (by omega)]

/-- The M-test bound: on `{z : ℂ | 5 ≤ ‖z‖}` we have `‖term j z‖ ≤ (1/5)^j`. -/
lemma norm_term_le (j : ℕ) (z : ℂ) (hz : z ∈ {z : ℂ | 5 ≤ ‖z‖}) :
    ‖term j z‖ ≤ (1 / 5 : ℝ) ^ j := by
  have hz5 : (5 : ℝ) ≤ ‖z‖ := hz
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num) hz5
  have hbound : ‖(1 : ℂ) / z‖ ≤ 1 / 5 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hz5
  unfold term
  split
  · simp
  · rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound j

lemma summable_geom : Summable (fun j : ℕ => (1 / 5 : ℝ) ^ j) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- **Weierstrass M-test**: the partial sums `∑_{j=1}^n (1/z)^j` converge uniformly on
`{z : ℂ | 5 ≤ ‖z‖}`. -/
theorem question_3 :
    ∃ f : ℂ → ℂ,
      TendstoUniformlyOn
        (fun n (z : ℂ) => ∑ j ∈ Finset.Icc 1 n, (1 / z) ^ j)
        f
        atTop
        { z : ℂ | 5 ≤ ‖z‖ } := by
  refine ⟨fun z => ∑' j : ℕ, term j z, ?_⟩
  have h : TendstoUniformlyOn (fun N (z : ℂ) => ∑ j ∈ Finset.range N, term j z)
      (fun z => ∑' j : ℕ, term j z) atTop { z : ℂ | 5 ≤ ‖z‖ } :=
    tendstoUniformlyOn_tsum_nat summable_geom (fun j z hz => norm_term_le j z hz)
  intro v hv
  have h' := h v hv
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [hshift.eventually h'] with n hn z hz
  simpa [sum_range_succ_term n z] using hn z hz

end UniformGeometric
