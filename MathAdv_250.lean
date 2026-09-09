import Mathlib

/-!
# Expected exit time of an asymmetric simple random walk

Let `S n = X 1 + ... + X n` be a simple random walk with `P (X i = 1) = p`,
`P (X i = -1) = 1 - p` and `p ≠ 1/2`, started at `0`, and for integers
`a ≤ -1` and `b ≥ 1` let `τ = min {n ≥ 1 : S n = a or S n = b}`.

The function `x ↦ E[τ | S 0 = x]` is characterised by first–step analysis: it is the unique
function `h : ℤ → ℝ` with

* `h a = 0`, `h b = 0`,
* `h x = 1 + p * h (x+1) + (1-p) * h (x-1)` for `a < x < b`.

In this file we

* define the explicit candidate `RandomWalk.expExitTime p a b`,
* prove that it solves the above system (`RandomWalk.expExitTime_left`,
  `RandomWalk.expExitTime_right`, `RandomWalk.expExitTime_recurrence`),
* prove that the system has at most one solution (`RandomWalk.exit_time_unique`),
* conclude that the value at the starting point `0` of any solution is
  `(a * (1 - r ^ b) + b * (r ^ a - 1)) / ((r ^ a - r ^ b) * (2 * p - 1))`
  with `r = (1 - p) / p` (`RandomWalk.expected_exit_time_eq`).
-/

open Finset

namespace RandomWalk

variable {p : ℝ} {a b : ℤ}

/-- The ratio `r = (1 - p) / p` appearing in the answer. -/
noncomputable def ratio (p : ℝ) : ℝ := (1 - p) / p

lemma ratio_pos (hp0 : 0 < p) (hp1 : p < 1) : 0 < ratio p :=
  div_pos (by linarith) hp0

lemma ratio_ne_one (hp0 : 0 < p) (hp : p ≠ 1 / 2) : ratio p ≠ 1 := by
  intro h
  rw [ratio, div_eq_one_iff_eq hp0.ne'] at h
  exact hp (by linarith)

lemma zpow_ratio_ne (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) (hab : a ≠ b) :
    ratio p ^ a ≠ ratio p ^ b := fun h =>
  hab ((zpow_right_inj₀ (ratio_pos hp0 hp1) (ratio_ne_one hp0 hp)).1 h)

/-- The characteristic identity `p * r ^ (x+1) + (1-p) * r ^ (x-1) = r ^ x`. -/
lemma ratio_zpow_step (hp0 : 0 < p) (hp1 : p < 1) (x : ℤ) :
    p * ratio p ^ (x + 1) + (1 - p) * ratio p ^ (x - 1) = ratio p ^ x := by
  have hr : ratio p ≠ 0 := (ratio_pos hp0 hp1).ne'
  have hp0' : p ≠ 0 := hp0.ne'
  have hq : (1 : ℝ) - p ≠ 0 := by linarith
  rw [zpow_add_one₀ hr, zpow_sub_one₀ hr, ratio]
  field_simp
  ring

/-- Every function of the form `x ↦ (c - x) / (2p-1) + B * r ^ x + C` solves the
first–step recurrence. -/
lemma affine_solution_recurrence (hp0 : 0 < p) (hp1 : p < 1) (h2 : 2 * p - 1 ≠ 0)
    (c B C : ℝ) (x : ℤ) :
    (c - (x : ℝ)) / (2 * p - 1) + B * ratio p ^ x + C
      = 1 + p * ((c - ((x : ℝ) + 1)) / (2 * p - 1) + B * ratio p ^ (x + 1) + C)
        + (1 - p) * ((c - ((x : ℝ) - 1)) / (2 * p - 1) + B * ratio p ^ (x - 1) + C) := by
  have hstep := ratio_zpow_step hp0 hp1 x
  have hu : (2 * p - 1) * (2 * p - 1)⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination hu - B * hstep

/-- The explicit solution of the first–step equations for the expected exit time of the
asymmetric random walk from the interval `[a, b]`, evaluated at the starting point `x`. -/
noncomputable def expExitTime (p : ℝ) (a b x : ℤ) : ℝ :=
  ((a : ℝ) - x) / (2 * p - 1) +
    (((a : ℝ) - b) / ((2 * p - 1) * (ratio p ^ a - ratio p ^ b))) * (ratio p ^ x - ratio p ^ a)

lemma expExitTime_left : expExitTime p a b a = 0 := by
  simp [expExitTime]

lemma expExitTime_right (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) (h2 : 2 * p - 1 ≠ 0)
    (hab : a ≠ b) : expExitTime p a b b = 0 := by
  have hne : ratio p ^ a - ratio p ^ b ≠ 0 := sub_ne_zero.mpr (zpow_ratio_ne hp0 hp1 hp hab)
  rw [expExitTime]
  field_simp
  ring

lemma expExitTime_recurrence (hp0 : 0 < p) (hp1 : p < 1) (h2 : 2 * p - 1 ≠ 0) (x : ℤ) :
    expExitTime p a b x
      = 1 + p * expExitTime p a b (x + 1) + (1 - p) * expExitTime p a b (x - 1) := by
  have key := affine_solution_recurrence hp0 hp1 h2 (a : ℝ)
      (((a : ℝ) - b) / ((2 * p - 1) * (ratio p ^ a - ratio p ^ b)))
      (-((((a : ℝ) - b) / ((2 * p - 1) * (ratio p ^ a - ratio p ^ b))) * ratio p ^ a)) x
  simp only [expExitTime]
  push_cast
  linear_combination key

/-- A solution of the homogeneous first–step recurrence vanishing at both endpoints
vanishes identically on `[a, b]`. -/
lemma homogeneous_eq_zero (hp0 : 0 < p) (hp1 : p < 1) (hab : a < b)
    (d : ℤ → ℝ) (hda : d a = 0) (hdb : d b = 0)
    (hrec : ∀ x, a < x → x < b → d x = p * d (x + 1) + (1 - p) * d (x - 1)) :
    ∀ x, a ≤ x → x ≤ b → d x = 0 := by
  have hp0' : p ≠ 0 := hp0.ne'
  have hrpos := ratio_pos hp0 hp1
  -- Step 1: the increments form a geometric sequence.
  have step1 : ∀ n : ℕ, (n : ℤ) + 1 ≤ b - a →
      d (a + (n : ℤ) + 1) - d (a + (n : ℤ)) = ratio p ^ n * d (a + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [hda]
    | succ m ih =>
        intro hm
        have hm' : (m : ℤ) + 1 ≤ b - a := by push_cast at hm ⊢; omega
        have ihm := ih hm'
        have hx1 : a < a + (m : ℤ) + 1 := by omega
        have hx2 : a + (m : ℤ) + 1 < b := by push_cast at hm; omega
        have hr := hrec (a + (m : ℤ) + 1) hx1 hx2
        have e1 : a + (m : ℤ) + 1 - 1 = a + (m : ℤ) := by ring
        rw [e1] at hr
        have : d (a + (m : ℤ) + 1 + 1) - d (a + (m : ℤ) + 1)
            = ratio p * (d (a + (m : ℤ) + 1) - d (a + (m : ℤ))) := by
          rw [ratio]
          field_simp
          linarith [hr]
        rw [show a + ((m + 1 : ℕ) : ℤ) + 1 = a + (m : ℤ) + 1 + 1 by push_cast; ring,
          show a + ((m + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 by push_cast; ring, this, ihm]
        ring
  -- Step 2: summing the increments.
  have step2 : ∀ n : ℕ, (n : ℤ) ≤ b - a →
      d (a + (n : ℤ)) = (∑ k ∈ range n, ratio p ^ k) * d (a + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [hda]
    | succ m ih =>
        intro hm
        have hm' : (m : ℤ) + 1 ≤ b - a := by push_cast at hm; omega
        have hm'' : (m : ℤ) ≤ b - a := by omega
        rw [show a + ((m + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 by push_cast; ring]
        rw [Finset.sum_range_succ]
        have := step1 m hm'
        rw [ih hm''] at this
        linarith [this]
  -- Step 3: `d (a+1) = 0`.
  have hn : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hsum : (0 : ℝ) < ∑ k ∈ range (b - a).toNat, ratio p ^ k := by
    apply Finset.sum_pos (fun k _ => pow_pos hrpos k)
    refine ⟨0, ?_⟩
    simp only [Finset.mem_range]
    omega
  have hd1 : d (a + 1) = 0 := by
    have h2 := step2 (b - a).toNat (by omega)
    rw [hn, show a + (b - a) = b by ring, hdb] at h2
    rcases mul_eq_zero.1 h2.symm with h | h
    · exact absurd h hsum.ne'
    · exact h
  -- Conclusion.
  intro x hax hxb
  have hx : ((x - a).toNat : ℤ) = x - a := Int.toNat_of_nonneg (by omega)
  have := step2 (x - a).toNat (by omega)
  rw [hx, show a + (x - a) = x by ring, hd1] at this
  simpa using this

/-- Uniqueness of the solution of the first–step equations for the expected exit time. -/
theorem exit_time_unique (hp0 : 0 < p) (hp1 : p < 1) (hab : a < b)
    (h g : ℤ → ℝ) (hha : h a = 0) (hhb : h b = 0)
    (hhrec : ∀ x, a < x → x < b → h x = 1 + p * h (x + 1) + (1 - p) * h (x - 1))
    (hga : g a = 0) (hgb : g b = 0)
    (hgrec : ∀ x, a < x → x < b → g x = 1 + p * g (x + 1) + (1 - p) * g (x - 1)) :
    ∀ x, a ≤ x → x ≤ b → h x = g x := by
  have := homogeneous_eq_zero hp0 hp1 hab (fun x => h x - g x) (by simp [hha, hga])
    (by simp [hhb, hgb])
    (by
      intro x hx1 hx2
      have h1 := hhrec x hx1 hx2
      have h2 := hgrec x hx1 hx2
      simp only
      linarith)
  intro x hax hxb
  have := this x hax hxb
  simp only at this
  linarith

/-- **Expected exit time of an asymmetric simple random walk.**
If `h` is the expected exit time function of the walk (characterised by first–step analysis:
`h a = h b = 0` and `h x = 1 + p * h (x+1) + (1-p) * h (x-1)` inside `(a, b)`), then the
expected exit time starting from `0` is
`(a (1 - r ^ b) + b (r ^ a - 1)) / ((r ^ a - r ^ b) (2p - 1))` with `r = (1-p)/p`. -/
theorem expected_exit_time_eq (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2)
    (ha : a ≤ -1) (hb : 1 ≤ b) (h : ℤ → ℝ) (hha : h a = 0) (hhb : h b = 0)
    (hrec : ∀ x, a < x → x < b → h x = 1 + p * h (x + 1) + (1 - p) * h (x - 1)) :
    h 0 = ((a : ℝ) * (1 - ratio p ^ b) + (b : ℝ) * (ratio p ^ a - 1)) /
      ((ratio p ^ a - ratio p ^ b) * (2 * p - 1)) := by
  have h2 : 2 * p - 1 ≠ 0 := by
    intro hc; exact hp (by linarith)
  have hab : a < b := by omega
  have hne : ratio p ^ a - ratio p ^ b ≠ 0 :=
    sub_ne_zero.mpr (zpow_ratio_ne hp0 hp1 hp hab.ne)
  have huniq := exit_time_unique hp0 hp1 hab h (expExitTime p a b) hha hhb hrec
    expExitTime_left (expExitTime_right hp0 hp1 hp h2 hab.ne)
    (fun x _ _ => expExitTime_recurrence hp0 hp1 h2 x) 0 (by omega) (by omega)
  rw [huniq, expExitTime]
  field_simp
  ring

/-- **Existence.** The system of first–step equations characterising the expected exit time
does have a solution, namely `expExitTime p a b`, and its value at the starting point `0`
is the announced closed form. -/
theorem exit_time_exists (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2)
    (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∃ h : ℤ → ℝ, h a = 0 ∧ h b = 0 ∧
      (∀ x, a < x → x < b → h x = 1 + p * h (x + 1) + (1 - p) * h (x - 1)) ∧
      h 0 = ((a : ℝ) * (1 - ratio p ^ b) + (b : ℝ) * (ratio p ^ a - 1)) /
        ((ratio p ^ a - ratio p ^ b) * (2 * p - 1)) := by
  have h2 : 2 * p - 1 ≠ 0 := fun hc => hp (by linarith)
  have hab : a < b := by omega
  refine ⟨expExitTime p a b, expExitTime_left, expExitTime_right hp0 hp1 hp h2 hab.ne,
    fun x _ _ => expExitTime_recurrence hp0 hp1 h2 x, ?_⟩
  exact expected_exit_time_eq hp0 hp1 hp ha hb _ expExitTime_left
    (expExitTime_right hp0 hp1 hp h2 hab.ne) (fun x _ _ => expExitTime_recurrence hp0 hp1 h2 x)

/-
The originally proposed formalisation was

  theorem problem_23
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hp_ne : p ≠ 1/2)
    (a b : ℤ) (ha : a ≤ -1) (hb : 1 ≤ b)
    (E_tau : ℝ) :
    let q := 1 - p
    let ρ := q / p
    let P_b := (1 - ρ ^ (a : ℝ)) / (ρ ^ (b : ℝ) - ρ ^ (a : ℝ))
    E_tau = (b * P_b + a * (1 - P_b)) / (2 * p - 1)

It is not provable (and indeed false): `E_tau` is a completely unconstrained real variable,
so the statement asserts that *every* real number equals the given expression.  Nothing in
the hypotheses ties `E_tau` to the random walk.  It is replaced above by
`expected_exit_time_eq`, where the expected exit time is pinned down by its defining
first-step (one-step conditioning) equations.  Note that the right-hand side above is the
same quantity: with `P_b = (1 - ρ^a)/(ρ^b - ρ^a)` the exit probability at `b`, one has
`(b * P_b + a * (1 - P_b)) / (2p-1) = (a (1 - ρ^b) + b (ρ^a - 1)) / ((ρ^a - ρ^b)(2p-1))`.
-/

/-- The two ways of writing the answer agree: `(b * P_b + a * (1 - P_b)) / (2p-1)` with
`P_b = (1 - r ^ a) / (r ^ b - r ^ a)` is the announced closed form. -/
lemma answer_forms_eq (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) (hab : a < b) :
    ((b : ℝ) * ((1 - ratio p ^ a) / (ratio p ^ b - ratio p ^ a))
        + (a : ℝ) * (1 - (1 - ratio p ^ a) / (ratio p ^ b - ratio p ^ a))) / (2 * p - 1)
      = ((a : ℝ) * (1 - ratio p ^ b) + (b : ℝ) * (ratio p ^ a - 1)) /
        ((ratio p ^ a - ratio p ^ b) * (2 * p - 1)) := by
  have h2 : 2 * p - 1 ≠ 0 := fun hc => hp (by linarith)
  have hne : ratio p ^ b - ratio p ^ a ≠ 0 :=
    sub_ne_zero.mpr (zpow_ratio_ne (a := b) (b := a) hp0 hp1 hp hab.ne')
  have hne' : ratio p ^ a - ratio p ^ b ≠ 0 := sub_ne_zero.mpr (zpow_ratio_ne hp0 hp1 hp hab.ne)
  field_simp
  ring

end RandomWalk

