import Mathlib

open Polynomial

/-- The minimal polynomial of the operator on `ℝ²` given by the matrix
`A = ![![-7, 8], ![-16, 17]]` is `λ² - 10λ + 9`.

The proof: `A² - 10A + 9I = 0`, so the minimal polynomial divides `X² - 10X + 9`;
and since `A` is not a scalar matrix, its minimal polynomial has degree at least `2`. -/
theorem question_11 :
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      ![
        ![-7, 8],
        ![-16, 17]
      ]
    minpoly ℝ A = (X ^ 2 - 10 * X + 9 : Polynomial ℝ) := by
  intro A
  set p : ℝ[X] := X ^ 2 - 10 * X + 9 with hp
  have hint : IsIntegral ℝ A := Algebra.IsIntegral.isIntegral A
  have hpdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hpm : p.Monic := by rw [hp]; monicity!
  -- `A` satisfies `p`
  have hp0 : (aeval A) p = 0 := by
    have h : (aeval A) p
        = A * A - (10 : ℝ) • A + (9 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      simp [hp, pow_two, Algebra.smul_def, map_ofNat]
    rw [h]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.one_apply] <;> norm_num
  have hdvd : minpoly ℝ A ∣ p := minpoly.dvd ℝ A hp0
  -- `A` is not a scalar matrix, so the minimal polynomial does not have degree one
  have hne : A ∉ (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ)).range := by
    rintro ⟨c, hc⟩
    have := congrArg (fun M => M 0 1) hc
    simp [A, Algebra.algebraMap_eq_smul_one] at this
  have _h1 : (minpoly ℝ A).natDegree ≠ 1 := fun h => hne (minpoly.natDegree_eq_one_iff.mp h)
  have _h0 : 0 < (minpoly ℝ A).natDegree := minpoly.natDegree_pos hint
  have hpne : p ≠ 0 := hpm.ne_zero
  have _hle : (minpoly ℝ A).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hpne
    omega
  have heq : (minpoly ℝ A).natDegree = 2 := by omega
  -- the cofactor is `1`
  obtain ⟨q, hq⟩ := hdvd
  have hmne : minpoly ℝ A ≠ 0 := minpoly.ne_zero hint
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hpne hq
  have hdq : q.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hmne hqne
    rw [← hq, hpdeg, heq] at hmul
    omega
  have hqm : q = 1 := by
    have hlead : q.leadingCoeff = 1 := by
      have h := hpm.leadingCoeff
      rw [hq, Polynomial.leadingCoeff_mul, (minpoly.monic hint).leadingCoeff, one_mul] at h
      exact h
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdq
    rw [hC] at hlead ⊢
    simp at hlead
    simp [hlead]
  rw [hq, hqm, mul_one]
