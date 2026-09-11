import Mathlib

open Set
open scoped BigOperators

def S : Set (ℝ × ℝ) :=
  {p | p = (0, 0) ∨ p = (2, 0) ∨ p = (0, 1)}

theorem convexHull_S :
    convexHull ℝ S =
      {p : ℝ × ℝ |
        p.1 ≥ 0 ∧
        p.2 ≥ 0 ∧
        p.1 / 2 + p.2 ≤ 1} := by

  let T : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ |
      p.1 ≥ 0 ∧
      p.2 ≥ 0 ∧
      p.1 / 2 + p.2 ≤ 1}

  change convexHull ℝ S = T

  apply Set.Subset.antisymm

  · -- convexHull S ⊆ T
    apply convexHull_min

    · intro p hp

      change
        0 ≤ p.1 ∧
        0 ≤ p.2 ∧
        p.1 / 2 + p.2 ≤ 1

      simp only [S] at hp

      rcases hp with h | h | h

      · subst p
        norm_num

      · subst p
        norm_num

      · subst p
        norm_num

    · -- T is convex
      rw [convex_iff_add_mem]

      intro p hp q hq a b ha hb hab

      change
        0 ≤ (a • p + b • q).1 ∧
        0 ≤ (a • p + b • q).2 ∧
        (a • p + b • q).1 / 2 +
            (a • p + b • q).2 ≤ 1

      change
        0 ≤ a * p.1 + b * q.1 ∧
        0 ≤ a * p.2 + b * q.2 ∧
        (a * p.1 + b * q.1) / 2 +
            (a * p.2 + b * q.2) ≤ 1

      rcases hp with ⟨hp1, hp2, hp3⟩
      rcases hq with ⟨hq1, hq2, hq3⟩

      constructor

      · exact add_nonneg
          (mul_nonneg ha hp1)
          (mul_nonneg hb hq1)

      constructor

      · exact add_nonneg
          (mul_nonneg ha hp2)
          (mul_nonneg hb hq2)

      · have hp3' :
            p.1 + 2 * p.2 ≤ 2 := by
          nlinarith [hp3]

        have hq3' :
            q.1 + 2 * q.2 ≤ 2 := by
          nlinarith [hq3]

        have ha' :
            a * (p.1 + 2 * p.2) ≤ a * 2 := by
          exact mul_le_mul_of_nonneg_left hp3' ha

        have hb' :
            b * (q.1 + 2 * q.2) ≤ b * 2 := by
          exact mul_le_mul_of_nonneg_left hq3' hb

        nlinarith [ha', hb', hab]

  · -- T ⊆ convexHull S
    intro p hp

    change
      0 ≤ p.1 ∧
      0 ≤ p.2 ∧
      p.1 / 2 + p.2 ≤ 1
      at hp

    let w : Fin 3 → ℝ :=
      ![
        1 - p.1 / 2 - p.2,
        p.1 / 2,
        p.2
      ]

    let z : Fin 3 → ℝ × ℝ :=
      ![
        (0, 0),
        (2, 0),
        (0, 1)
      ]

    apply
      mem_convexHull_of_exists_fintype
        w z

    · -- weights are nonnegative
      intro i
      fin_cases i

      · simp [w]
        linarith [hp.2.2]

      · simp [w]
        linarith [hp.1]

      · simp [w]
        exact hp.2.1

    · -- weights sum to 1
      rw [Fin.sum_univ_three]
      simp [w]
      ring

    · -- vertices belong to S
      intro i
      fin_cases i <;> simp [z, S]

    · -- weighted sum equals p
      rw [Fin.sum_univ_three]

      apply Prod.ext

      · simp [w, z]

      · simp [w, z]
