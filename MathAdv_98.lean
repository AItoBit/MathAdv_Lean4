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

/-- The Legendre polynomials, defined by Bonnet's recurrence relation
`(n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x)`. -/
noncomputable def legendreP : ℕ → ℝ → ℝ
  | 0,   _ => 1
  | 1,   x => x
  | n+2, x =>
      let n' : ℝ := n
      ((2 * n' + 3) * x * legendreP (n+1) x - (n' + 1) * legendreP n x) / (n' + 2)

noncomputable def P (n : ℕ) (x : ℝ) : ℝ :=
  legendreP n x

/-- Bonnet's recurrence relation, in explicit form. -/
lemma legendreP_rec (k : ℕ) (x : ℝ) :
    legendreP (k + 2) x =
      ((2 * (k : ℝ) + 3) * x * legendreP (k + 1) x - ((k : ℝ) + 1) * legendreP k x)
        / ((k : ℝ) + 2) := by
  simp [legendreP]

/-- Every Legendre polynomial is a differentiable function on `ℝ`. -/
lemma legendreP_diff : ∀ n : ℕ, Differentiable ℝ (fun x => legendreP n x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [legendreP]
    | 1 => simp [legendreP]
    | (k + 2) =>
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      simp only [legendreP]
      fun_prop

/-- The derivative of the recurrence relation. -/
lemma deriv_legendreP_add_two (k : ℕ) (x : ℝ) :
    deriv (fun y => legendreP (k + 2) y) x =
      ((2 * (k : ℝ) + 3) * (legendreP (k + 1) x + x * deriv (fun y => legendreP (k + 1) y) x)
        - ((k : ℝ) + 1) * deriv (fun y => legendreP k y) x) / ((k : ℝ) + 2) := by
  have h1 : HasDerivAt (fun y => legendreP (k + 1) y)
      (deriv (fun y => legendreP (k + 1) y) x) x := ((legendreP_diff (k + 1)) x).hasDerivAt
  have h2 : HasDerivAt (fun y => legendreP k y)
      (deriv (fun y => legendreP k y) x) x := ((legendreP_diff k) x).hasDerivAt
  have key : HasDerivAt (fun y => legendreP (k + 2) y)
      (((2 * (k : ℝ) + 3) * (legendreP (k + 1) x + x * deriv (fun y => legendreP (k + 1) y) x)
        - ((k : ℝ) + 1) * deriv (fun y => legendreP k y) x) / ((k : ℝ) + 2)) x := by
    have e : (fun y => legendreP (k + 2) y) = fun y =>
        ((2 * (k : ℝ) + 3) * y * legendreP (k + 1) y - ((k : ℝ) + 1) * legendreP k y)
          / ((k : ℝ) + 2) := by
      funext y; simp [legendreP]
    rw [e]
    have hx : HasDerivAt (fun y : ℝ => (2 * (k : ℝ) + 3) * y) (2 * (k : ℝ) + 3) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * (k : ℝ) + 3)
    have := ((hx.mul h1).sub (h2.const_mul ((k : ℝ) + 1))).div_const ((k : ℝ) + 2)
    convert this using 2
    ring
  exact key.deriv

/-- The two classical companion identities
`x P'_{n+1} - P'_n = (n+1) P_{n+1}` and `P'_{n+1} = x P'_n + (n+1) P_n`,
proved simultaneously by induction on `n`. -/
lemma legendreP_deriv_pair : ∀ (m : ℕ) (x : ℝ),
    (x * deriv (fun y => legendreP (m + 1) y) x - deriv (fun y => legendreP m y) x
        = ((m : ℝ) + 1) * legendreP (m + 1) x)
      ∧ (deriv (fun y => legendreP (m + 1) y) x
        = x * deriv (fun y => legendreP m y) x + ((m : ℝ) + 1) * legendreP m x) := by
  intro m
  induction m with
  | zero =>
      intro x
      constructor
      · simp [legendreP]
      · simp [legendreP]
  | succ m ih =>
      intro x
      obtain ⟨hB, hC⟩ := ih x
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      have hd : deriv (fun y => legendreP (m + 2) y) x * ((m : ℝ) + 2)
          = (2 * (m : ℝ) + 3)
              * (legendreP (m + 1) x + x * deriv (fun y => legendreP (m + 1) y) x)
            - ((m : ℝ) + 1) * deriv (fun y => legendreP m y) x := by
        rw [deriv_legendreP_add_two m x]
        field_simp
      have hrec : legendreP (m + 2) x * ((m : ℝ) + 2)
          = (2 * (m : ℝ) + 3) * x * legendreP (m + 1) x - ((m : ℝ) + 1) * legendreP m x := by
        rw [legendreP_rec m x]
        field_simp
      set a := deriv (fun y => legendreP m y) x with ha
      set b := deriv (fun y => legendreP (m + 1) y) x with hb
      set c := deriv (fun y => legendreP (m + 2) y) x with hc
      set p := legendreP m x with hp
      set q := legendreP (m + 1) x with hq
      set r := legendreP (m + 2) x with hr
      -- first identity of the pair at `m+1`
      have hC1 : c = x * b + ((m : ℝ) + 2) * q := by
        refine mul_right_cancel₀ hm2 ?_
        linear_combination hd + ((m : ℝ) + 1) * hB
      -- the auxiliary identity `(x²-1) P'_{m+1} = (m+1) (x P_{m+1} - P_m)`
      have hD : (x ^ 2 - 1) * b = ((m : ℝ) + 1) * (x * q - p) := by
        linear_combination x * hB - hC
      have hB1 : x * c - b = ((m : ℝ) + 2) * r := by
        refine mul_right_cancel₀ hm2 ?_
        linear_combination x * ((m : ℝ) + 2) * hC1 + ((m : ℝ) + 2) * hD - ((m : ℝ) + 2) * hrec
      refine ⟨?_, ?_⟩
      · push_cast
        rw [show ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) by ring]
        exact hB1
      · push_cast
        rw [show ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) by ring]
        exact hC1

/-- **The Legendre derivative identity**:
`P'_{n+1}(x) - P'_{n-1}(x) = (2n+1) P_n(x)` for all `n ≥ 1`. -/
theorem brown_8 :
  ∀ n ≥ 1, ∀ x : ℝ,
    deriv (fun x => P (n + 1) x) x
      - deriv (fun x => P (n - 1) x) x
    = (2 * (n : ℝ) + 1) * P n x := by
  intro n hn x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hB, _⟩ := legendreP_deriv_pair m x
  obtain ⟨_, hC'⟩ := legendreP_deriv_pair (m + 1) x
  simp only [P, Nat.add_sub_cancel]
  push_cast
  push_cast at hC'
  rw [show (m + 1 + 1) = (m + 2) from rfl] at hC' ⊢
  linarith [hB, hC']

-- Sanity checks: the first few Legendre polynomials.
example (x : ℝ) : legendreP 2 x = (3 * x ^ 2 - 1) / 2 := by
  rw [legendreP_rec 0 x]; norm_num [legendreP]; ring

example (x : ℝ) : legendreP 3 x = (5 * x ^ 3 - 3 * x) / 2 := by
  rw [legendreP_rec 1 x, legendreP_rec 0 x]; norm_num [legendreP]; ring
