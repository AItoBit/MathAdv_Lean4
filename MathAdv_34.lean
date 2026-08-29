import Mathlib

/-!
# Closest points on the parabola `y = x² + 1` to the point `(0, 2)`

The points on the curve `y = x² + 1` that are closest (in the Euclidean plane distance)
to `(0, 2)` are exactly `(1/√2, 3/2)` and `(-1/√2, 3/2)`.
-/

open Real

/-- The squared Euclidean distance from a point of the plane to `(0, 2)`. -/
noncomputable def sqDistTo02 (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + (p.2 - 2) ^ 2

/-- Euclidean distance from a point of the plane to `(0, 2)`. -/
noncomputable def euclDistTo02 (p : ℝ × ℝ) : ℝ := Real.sqrt (sqDistTo02 p)

/-- On the parabola, the squared distance to `(0,2)` equals `(x² - 1/2)² + 3/4`. -/
lemma sqDistTo02_parabola {p : ℝ × ℝ} (hp : p.2 = p.1 ^ 2 + 1) :
    sqDistTo02 p = (p.1 ^ 2 - 1 / 2) ^ 2 + 3 / 4 := by
  simp only [sqDistTo02, hp]; ring

/-- **Main theorem.** The points of the parabola `y = x² + 1` closest to `(0, 2)` for the
Euclidean distance are exactly `(±1/√2, 3/2)`. -/
theorem dawkins_4_9_3 :
    { p : ℝ × ℝ | p.2 = p.1 ^ 2 + 1 ∧
        ∀ q : ℝ × ℝ, q.2 = q.1 ^ 2 + 1 → euclDistTo02 q ≥ euclDistTo02 p } =
      { (1 / Real.sqrt 2, 3 / 2), (-1 / Real.sqrt 2, 3 / 2) } := by
  have hs2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hval : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, hsq2]; norm_num
  have hvaln : ((-1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, hsq2]; norm_num
  -- the minimal value of the squared distance is 3/4
  have hmin : ∀ q : ℝ × ℝ, q.2 = q.1 ^ 2 + 1 → sqDistTo02 q ≥ 3 / 4 := by
    intro q hq
    rw [sqDistTo02_parabola hq]
    nlinarith [sq_nonneg (q.1 ^ 2 - 1 / 2)]
  have key : ∀ x y : ℝ, x ^ 2 = 1 / 2 → y = 3 / 2 →
      (y = x ^ 2 + 1 ∧ ∀ q : ℝ × ℝ, q.2 = q.1 ^ 2 + 1 →
        euclDistTo02 q ≥ euclDistTo02 (x, y)) := by
    intro x y hx hy
    refine ⟨by rw [hx, hy]; norm_num, ?_⟩
    intro q hq
    have h1 : sqDistTo02 (x, y) = 3 / 4 := by
      simp only [sqDistTo02, hy, hx]; norm_num
    have h2 : sqDistTo02 q ≥ 3 / 4 := hmin q hq
    unfold euclDistTo02
    rw [h1]
    exact Real.sqrt_le_sqrt h2
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hmin'⟩
    have hcand := (key (1 / Real.sqrt 2) (3 / 2) hval rfl).1
    have hcand2 : sqDistTo02 (1 / Real.sqrt 2, 3 / 2) = 3 / 4 := by
      simp only [sqDistTo02, hval]; norm_num
    have hle : Real.sqrt (sqDistTo02 (x, y)) ≤ Real.sqrt (3 / 4) := by
      have h := hmin' (1 / Real.sqrt 2, 3 / 2) hcand
      unfold euclDistTo02 at h
      rw [hcand2] at h
      exact h
    have hple : sqDistTo02 (x, y) ≤ 3 / 4 := by
      by_contra hcon
      push Not at hcon
      exact absurd hle (not_le.mpr (Real.sqrt_lt_sqrt (by norm_num) hcon))
    have hx : x ^ 2 = 1 / 2 := by
      rw [sqDistTo02_parabola (p := (x, y)) hp] at hple
      nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
    have hy : y = 3 / 2 := by rw [hp, hx]; norm_num
    have hfac : (x - 1 / Real.sqrt 2) * (x + 1 / Real.sqrt 2) = 0 := by
      have h0 : x ^ 2 - (1 / Real.sqrt 2) ^ 2 = 0 := by rw [hx, hval]; ring
      nlinarith [h0]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl ⟨by linarith, hy⟩
    · refine Or.inr ⟨?_, hy⟩
      have hx' : x = -(1 / Real.sqrt 2) := by linarith
      rw [hx']; ring
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact key x y (by rw [h1]; exact hval) h2
    · exact key x y (by rw [h1]; exact hvaln) h2

/-- The originally proposed statement, which uses the supremum metric of `ℝ × ℝ`, is false. -/
theorem dawkins_4_9_3_sup_dist_false :
    { p : ℝ × ℝ | p.2 = p.1 ^ 2 + 1 ∧
        ∀ q : ℝ × ℝ, q.2 = q.1 ^ 2 + 1 → dist q (0, 2) ≥ dist p (0, 2) } ≠
      { (1 / Real.sqrt 2, 3 / 2), (-1 / Real.sqrt 2, 3 / 2) } := by
  intro hEq
  have hs2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs5 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  -- the point (1/√2, 3/2) belongs to the right-hand side, hence to the left-hand side
  have hmem : ((1 : ℝ) / Real.sqrt 2, (3 : ℝ) / 2) ∈
      { p : ℝ × ℝ | p.2 = p.1 ^ 2 + 1 ∧
        ∀ q : ℝ × ℝ, q.2 = q.1 ^ 2 + 1 → dist q (0, 2) ≥ dist p (0, 2) } := by
    rw [hEq]; left; rfl
  obtain ⟨-, hmin⟩ := hmem
  -- the golden-ratio point beats it
  set g : ℝ := (Real.sqrt 5 - 1) / 2 with hg
  have hg0 : 0 < g := by
    have : (1 : ℝ) < Real.sqrt 5 := by nlinarith
    simp only [hg]; linarith
  have hgsq : g ^ 2 = 1 - g := by
    simp only [hg]; nlinarith [hsq5]
  have hq := hmin (g, g ^ 2 + 1) rfl
  have hd1 : dist ((g, g ^ 2 + 1) : ℝ × ℝ) (0, 2) = g := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have h1 : |g - 0| = g := by rw [sub_zero, abs_of_pos hg0]
    have h2 : |g ^ 2 + 1 - 2| = g := by
      rw [hgsq]; rw [show (1 : ℝ) - g + 1 - 2 = -g by ring, abs_neg, abs_of_pos hg0]
    rw [h1, h2, max_self]
  have hd2 : dist (((1 : ℝ) / Real.sqrt 2, (3 : ℝ) / 2) : ℝ × ℝ) (0, 2) = 1 / Real.sqrt 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have h1 : |1 / Real.sqrt 2 - 0| = 1 / Real.sqrt 2 := by
      rw [sub_zero, abs_of_pos (by positivity)]
    have h2 : |(3 : ℝ) / 2 - 2| = 1 / 2 := by norm_num [abs_of_nonpos]
    rw [h1, h2, max_eq_left]
    rw [le_div_iff₀ hs2]
    nlinarith
  rw [hd1, hd2] at hq
  -- but g < 1/√2, contradiction
  have : g < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ hs2]
    have h5 : Real.sqrt 5 < 3 := by nlinarith
    have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
    nlinarith
  linarith
