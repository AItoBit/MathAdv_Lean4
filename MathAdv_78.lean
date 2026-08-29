import Mathlib

/-!
# The argument principle for polynomials

Let `p(z) = aₙ zⁿ + ⋯ + a₀` with `aₙ ≠ 0`.  We show there is `R > 0` such that, for the
positively oriented circle `C : |z| = R`,
`∮_C p'(z)/p(z) dz = 2nπi`.

The proof is the standard one: over `ℂ` the polynomial splits, so
`p'(z)/p(z) = Σ_{r a root of p, with multiplicity} 1/(z - r)`,
and each term integrates to `2πi` once `R` exceeds the modulus of every root.
-/

open Complex Metric Polynomial intervalIntegral

open scoped Real

namespace ArgumentPrinciple

/-- Circle integrability of a finite sum of simple poles all lying strictly inside the circle. -/
lemma circleIntegrable_list_inv (L : List ℂ) {R : ℝ} (h : ∀ r ∈ L, ‖r‖ < R) :
    CircleIntegrable (fun z => (L.map fun r => (z - r)⁻¹).sum) 0 R := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact circleIntegrable_const (0 : ℂ) 0 R
  | cons a L ih =>
      have ha : ‖a‖ < R := h a (List.mem_cons_self ..)
      have hR : 0 < R := lt_of_le_of_lt (norm_nonneg a) ha
      have h1 : CircleIntegrable (fun z => (z - a)⁻¹) 0 R := by
        refine circleIntegrable_sub_inv_iff.mpr (Or.inr ?_)
        simp only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR]
        exact ne_of_lt ha
      have h2 := ih fun r hr => h r (List.mem_cons_of_mem _ hr)
      exact h1.add h2

/-- Integral of a finite sum of simple poles all lying strictly inside the circle. -/
lemma circleIntegral_list_inv (L : List ℂ) {R : ℝ} (h : ∀ r ∈ L, ‖r‖ < R) :
    (∮ z in C(0, R), (L.map fun r => (z - r)⁻¹).sum)
      = (L.length : ℂ) * (2 * Real.pi * I) := by
  induction L with
  | nil => simp [circleIntegral]
  | cons a L ih =>
      have ha : ‖a‖ < R := h a (List.mem_cons_self ..)
      have hR : 0 < R := lt_of_le_of_lt (norm_nonneg a) ha
      have h1 : CircleIntegrable (fun z => (z - a)⁻¹) 0 R := by
        refine circleIntegrable_sub_inv_iff.mpr (Or.inr ?_)
        simp only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR]
        exact ne_of_lt ha
      have hL : ∀ r ∈ L, ‖r‖ < R := fun r hr => h r (List.mem_cons_of_mem _ hr)
      have h2 := circleIntegrable_list_inv L hL
      have hsplit : (∮ z in C(0, R), ((z - a)⁻¹ + (L.map fun r => (z - r)⁻¹).sum))
          = (∮ z in C(0, R), (z - a)⁻¹) + ∮ z in C(0, R), (L.map fun r => (z - r)⁻¹).sum :=
        circleIntegral.integral_add h1 h2
      have hmem : a ∈ ball (0 : ℂ) R := by simpa [Metric.mem_ball, dist_eq_norm] using ha
      have hone : (∮ z in C(0, R), (z - a)⁻¹) = 2 * Real.pi * I :=
        circleIntegral.integral_sub_inv_of_mem_ball hmem
      have := ih hL
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hsplit, hone, this]
      push_cast
      ring

/-- **The argument principle for polynomials.**  If `p` has degree `n` (and nonzero leading
coefficient), then for a large enough radius `R` the integral of the logarithmic derivative
`p'/p` over the positively oriented circle `|z| = R` equals `2nπi`.

The hypothesis `hlead : p.leadingCoeff ≠ 0` is kept because it was part of the requested
statement, but it is not needed: it already follows from `p.degree = n`.

(Multiple-choice companion question: the relevant tool is (a), the argument principle.) -/
theorem question_4
    (p : Polynomial ℂ) (n : ℕ)
    (hdeg : p.degree = n)
    (_hlead : p.leadingCoeff ≠ 0) :
    ∃ R > 0,
      (∮ z in C(0, R),
        (p.derivative.eval z) / (p.eval z)) =
        (2 * (n : ℂ)) * (Real.pi : ℂ) * Complex.I := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  have hnd : p.natDegree = n := natDegree_eq_of_degree_eq_some hdeg
  have hsplits : p.Splits :=
    Polynomial.splits_iff_card_roots.mpr IsAlgClosed.card_roots_eq_natDegree
  set L : List ℂ := p.roots.toList with hLdef
  set R : ℝ := 1 + (L.map fun r => ‖r‖).sum with hRdef
  have hsum_nonneg : 0 ≤ (L.map fun r => ‖r‖).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact norm_nonneg r
  have hR : 0 < R := by positivity
  have hroots : ∀ r ∈ L, ‖r‖ < R := by
    intro r hr
    have : ‖r‖ ≤ (L.map fun r => ‖r‖).sum := by
      refine List.single_le_sum ?_ _ (List.mem_map_of_mem hr)
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨s, _, rfl⟩ := hx
      exact norm_nonneg s
    simpa [hRdef] using lt_of_le_of_lt this (by linarith)
  refine ⟨R, hR, ?_⟩
  have hcongr : ∀ z ∈ sphere (0 : ℂ) R,
      p.derivative.eval z / p.eval z = (L.map fun r => (z - r)⁻¹).sum := by
    intro z hz
    have hznorm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hzne : p.eval z ≠ 0 := by
      intro hzero
      have : z ∈ p.roots := by
        rw [mem_roots hp0]
        exact hzero
      have hzL : z ∈ L := by rwa [hLdef, Multiset.mem_toList]
      exact absurd hznorm (ne_of_lt (hroots z hzL))
    rw [hsplits.eval_derivative_div_eval_of_ne_zero hzne]
    rw [hLdef]
    rw [show (Multiset.map (fun w => 1 / (z - w)) p.roots).sum
        = ((p.roots.toList.map fun w => (z - w)⁻¹) : List ℂ).sum by
      conv_lhs => rw [← Multiset.coe_toList p.roots]
      simp [one_div]]
  rw [circleIntegral.integral_congr hR.le hcongr, circleIntegral_list_inv L hroots]
  have hlen : (L.length : ℂ) = (n : ℂ) := by
    have : L.length = p.natDegree := by
      rw [hLdef, Multiset.length_toList]
      exact IsAlgClosed.card_roots_eq_natDegree
    rw [this, hnd]
  rw [hlen]
  ring

end ArgumentPrinciple
