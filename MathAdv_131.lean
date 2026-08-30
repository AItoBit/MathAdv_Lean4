import Mathlib
import RequestProject.WeightedSpace

/-!
# Dual of the weighted sequence space `h₂`

We consider the weighted sequence spaces
`h_{±2} = { c : ℕ → ℂ | ∑ j, (j+1)^{±4} |c j|² < ∞ }`
(the index shift `j ↦ j+1` accounts for the fact that our sequences are indexed
starting at `0` while the problem indexes them starting at `1`).

The main result `melrose_sp2009_11` shows that every linear functional on `h₂`
which is bounded for the `h₂` norm is given by pairing with an element of `h₋₂`.
-/

open Filter Topology Finset
open scoped ComplexConjugate

/-- Membership in the weighted space `h₂`. -/
def mem_h2 (c : ℕ → ℂ) : Prop :=
  Summable (fun j : ℕ ↦ ((↑j + 1 : ℝ)^4) * ‖c j‖^2)

/-- Membership in the weighted space `h₋₂`. -/
def mem_hNeg2 (d : ℕ → ℂ) : Prop :=
  Summable (fun j : ℕ ↦ ((↑j + 1 : ℝ)^(-4 : ℝ)) * ‖d j‖^2)

/-- The norm of the weighted space `h₂`. -/
noncomputable def h2Norm (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' j : ℕ, ((↑j + 1 : ℝ)^4) * ‖c j‖^2)

/-- The norm of the weighted space `h₋₂`. -/
noncomputable def hNeg2Norm (d : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' j : ℕ, ((↑j + 1 : ℝ)^(-4 : ℝ)) * ‖d j‖^2)

namespace Melrose

noncomputable section

lemma one_add_pos (j : ℕ) : (0:ℝ) < (j:ℝ) + 1 := by positivity

lemma rpow_neg_four (j : ℕ) : ((j:ℝ)+1)^(-4:ℝ) = (((j:ℝ)+1)^(4:ℕ))⁻¹ := by
  rw [show (-4:ℝ) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg (one_add_pos j).le,
    Real.rpow_natCast]

/-- The candidate representing sequence: `d j = T (δ j)`. -/
def dseq (T : (ℕ → ℂ) → ℂ) (j : ℕ) : ℂ := T (fun k => if k = j then 1 else 0)

/-- Truncation of a sequence to its first `N` entries. -/
def trunc (c : ℕ → ℂ) (N : ℕ) : ℕ → ℂ := fun k => if k < N then c k else 0

/-- The tail of a sequence after its first `N` entries. -/
def tl (c : ℕ → ℂ) (N : ℕ) : ℕ → ℂ := fun k => if k < N then 0 else c k

variable {T : (ℕ → ℂ) → ℂ}

lemma map_zero (h_smul : ∀ (α : ℂ) c, T (α • c) = α * T c) : T 0 = 0 := by
  have := h_smul 0 0
  simpa using this

lemma trunc_add_tl (c : ℕ → ℂ) (N : ℕ) : trunc c N + tl c N = c := by
  funext k
  by_cases h : k < N <;> simp [trunc, tl, h]

/-- Finite additivity: `T` applied to a truncation is the corresponding finite sum. -/
lemma T_trunc (h_add : ∀ c₁ c₂, T (c₁ + c₂) = T c₁ + T c₂)
    (h_smul : ∀ (α : ℂ) c, T (α • c) = α * T c) (c : ℕ → ℂ) (N : ℕ) :
    T (trunc c N) = ∑ j ∈ Finset.range N, c j * dseq T j := by
  induction N with
  | zero => simpa [trunc] using map_zero h_smul
  | succ N ih =>
      have hsplit : trunc c (N+1) = trunc c N + c N • (fun k => if k = N then (1:ℂ) else 0) := by
        funext k
        rcases lt_trichotomy k N with h | h | h
        · simp [trunc, h, Nat.lt_succ_of_lt h, Nat.ne_of_lt h]
        · subst h; simp [trunc]
        · have h1 : ¬ k < N := by omega
          have h2 : ¬ k < N + 1 := by omega
          have h3 : k ≠ N := by omega
          simp [trunc, h1, h2, h3]
      rw [hsplit, h_add, h_smul, ih, Finset.sum_range_succ, dseq]

/-- A finitely supported sequence lies in `h₂`. -/
lemma mem_h2_of_support (c : ℕ → ℂ) (N : ℕ) (hc : ∀ k, N ≤ k → c k = 0) : mem_h2 c := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  simp [hc k hk]

lemma h2Norm_of_support (c : ℕ → ℂ) (N : ℕ) (hc : ∀ k, N ≤ k → c k = 0) :
    h2Norm c = Real.sqrt (∑ j ∈ Finset.range N, ((↑j + 1 : ℝ)^4) * ‖c j‖^2) := by
  unfold h2Norm
  congr 1
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  simp [hc k hk]

lemma conj_mul_self (z : ℂ) : conj z * z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- Step 1: the sequence `d j = T (δ j)` lies in `h₋₂`. -/
lemma dseq_mem_hNeg2 (h_add : ∀ c₁ c₂, T (c₁ + c₂) = T c₁ + T c₂)
    (h_smul : ∀ (α : ℂ) c, T (α • c) = α * T c) {C : ℝ}
    (hb : ∀ c, mem_h2 c → ‖T c‖ ≤ C * h2Norm c) : mem_hNeg2 (dseq T) := by
  set d := dseq T with hd
  refine summable_of_sum_range_le (c := C^2) (fun n => by positivity) ?_
  intro N
  set S : ℝ := ∑ j ∈ Finset.range N, ((↑j + 1 : ℝ)^(-4 : ℝ)) * ‖d j‖^2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => by positivity)
  -- the test sequence
  set c : ℕ → ℂ := fun k => ((((k:ℝ)+1)^(-4:ℝ) : ℝ) : ℂ) * conj (d k) with hc
  have hsupp : ∀ k, N ≤ k → trunc c N k = 0 := by
    intro k hk; simp [trunc, Nat.not_lt.2 hk]
  have hmem : mem_h2 (trunc c N) := mem_h2_of_support _ N hsupp
  -- value of T
  have hval : T (trunc c N) = (S : ℂ) := by
    rw [T_trunc h_add h_smul]
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : conj (d j) * d j = ((‖d j‖^2 : ℝ) : ℂ) := conj_mul_self _
    simp only [hc, ← hd, mul_assoc, h1]
    push_cast
    ring
  -- the h₂ norm of the test sequence
  have hnorm : h2Norm (trunc c N) = Real.sqrt S := by
    rw [h2Norm_of_support _ N hsupp, hS]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    have hjt : trunc c N j = c j := by simp [trunc, hj]
    have hpos : (0:ℝ) < ((j:ℝ)+1)^(4:ℕ) := by positivity
    rw [hjt, hc]
    simp only [norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs,
      rpow_neg_four j, abs_of_nonneg (le_of_lt (inv_pos.2 hpos))]
    field_simp
  have hle : S ≤ C * Real.sqrt S := by
    have := hb _ hmem
    rw [hval, hnorm] at this
    simpa [Complex.norm_real, abs_of_nonneg hS0] using this
  nlinarith [Real.sq_sqrt hS0, Real.sqrt_nonneg S]

/-- Weighted AM-GM: the pairing is absolutely convergent term by term. -/
lemma norm_mul_le_half (x y : ℂ) (j : ℕ) :
    ‖x * y‖ ≤ (1/2) * (((j:ℝ)+1)^(4:ℕ) * ‖x‖^2 + ((j:ℝ)+1)^(-4:ℝ) * ‖y‖^2) := by
  set a : ℝ := ((j:ℝ)+1)^(2:ℕ) with ha
  have hpos : (0:ℝ) < a := by rw [ha]; positivity
  have ha4 : ((j:ℝ)+1)^(4:ℕ) = a^2 := by rw [ha, ← pow_mul]
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hneg : ((j:ℝ)+1)^(-4:ℝ) = (a⁻¹)^2 := by
    rw [rpow_neg_four, ha4, inv_pow]
  rw [norm_mul, ha4, hneg]
  have h := sq_nonneg (a * ‖x‖ - a⁻¹ * ‖y‖)
  have expand : (a * ‖x‖ - a⁻¹ * ‖y‖)^2
      = a^2 * ‖x‖^2 + (a⁻¹)^2 * ‖y‖^2 - 2 * (a * a⁻¹) * (‖x‖ * ‖y‖) := by ring
  rw [expand, hinv] at h
  linarith

/-- The pairing `∑ c j * d j` converges absolutely for `c ∈ h₂`, `d ∈ h₋₂`. -/
lemma summable_pairing {c d : ℕ → ℂ} (hc : mem_h2 c) (hd : mem_hNeg2 d) :
    Summable (fun j => c j * d j) := by
  apply Summable.of_norm
  have hsum : Summable (fun j : ℕ => (1/2 : ℝ) *
      (((j:ℝ)+1)^(4:ℕ) * ‖c j‖^2 + ((j:ℝ)+1)^(-4:ℝ) * ‖d j‖^2)) :=
    ((hc.add hd).mul_left _)
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => norm_mul_le_half (c j) (d j) j) hsum

/-- The tail of a sequence in `h₂` lies in `h₂`. -/
lemma mem_h2_tl {c : ℕ → ℂ} (hc : mem_h2 c) (N : ℕ) : mem_h2 (tl c N) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hc
  by_cases h : j < N <;> simp [tl, h]
  positivity

/-- The `h₂`-norm of the tails of a sequence in `h₂` tends to `0`. -/
lemma tendsto_h2Norm_tl {c : ℕ → ℂ} (hc : mem_h2 c) :
    Tendsto (fun N => h2Norm (tl c N)) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun j => ((↑j + 1 : ℝ)^4) * ‖c j‖^2 with hf
  have hfnn : ∀ j, 0 ≤ f j := fun j => by rw [hf]; positivity
  have key : ∀ N, h2Norm (tl c N) = Real.sqrt ((∑' j, f j) - ∑ j ∈ Finset.range N, f j) := by
    intro N
    have hpt : ∀ j, ((↑j + 1 : ℝ)^4) * ‖tl c N j‖^2 = (if j < N then 0 else f j) := by
      intro j; by_cases h : j < N <;> simp [tl, h, hf]
    have he1 : Summable (fun j : ℕ => if j < N then f j else 0) := by
      apply summable_of_ne_finset_zero (s := Finset.range N)
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [Nat.not_lt.2 hk]
    have he2 : Summable (fun j : ℕ => if j < N then 0 else f j) := by
      refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hc
      · by_cases h : j < N
        · simp only [if_pos h]; exact le_rfl
        · simpa only [if_neg h] using hfnn j
      · by_cases h : j < N
        · simpa only [if_pos h] using hfnn j
        · simp only [if_neg h]; exact le_rfl
    have hsplit : (∑' j, f j) = (∑ j ∈ Finset.range N, f j) + ∑' j, (if j < N then 0 else f j) := by
      have : (∑' j, f j)
          = ∑' j, ((if j < N then f j else 0) + (if j < N then 0 else f j)) := by
        refine tsum_congr (fun j => ?_)
        by_cases h : j < N <;> simp [h]
      rw [this, he1.tsum_add he2]
      congr 1
      rw [tsum_eq_sum (s := Finset.range N) (fun k hk => by
        simp only [Finset.mem_range, not_lt] at hk; simp [Nat.not_lt.2 hk])]
      exact Finset.sum_congr rfl (fun j hj => by simp [Finset.mem_range.1 hj])
    unfold h2Norm
    rw [tsum_congr hpt, hsplit]
    ring_nf
  rw [funext key]
  have : Tendsto (fun N => (∑' j, f j) - ∑ j ∈ Finset.range N, f j) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ∑ j ∈ Finset.range N, f j) atTop (𝓝 (∑' j, f j)) :=
      hc.hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := (∑' j, f j)) (f := atTop (α := ℕ))).sub h1
  simpa using (Real.continuous_sqrt.tendsto 0).comp this

/-- Step 2: the bounded functional is given by pairing with `dseq T`. -/
lemma repr_of_bdd (h_add : ∀ c₁ c₂, T (c₁ + c₂) = T c₁ + T c₂)
    (h_smul : ∀ (α : ℂ) c, T (α • c) = α * T c) {C : ℝ}
    (hb : ∀ c, mem_h2 c → ‖T c‖ ≤ C * h2Norm c) (hd : mem_hNeg2 (dseq T))
    (c : ℕ → ℂ) (hc : mem_h2 c) : T c = ∑' j, c j * dseq T j := by
  have hsum := summable_pairing hc hd
  have hlim1 : Tendsto (fun N => ∑ j ∈ Finset.range N, c j * dseq T j) atTop
      (𝓝 (∑' j, c j * dseq T j)) := hsum.hasSum.tendsto_sum_nat
  have hsplitT : ∀ N, T c = (∑ j ∈ Finset.range N, c j * dseq T j) + T (tl c N) := by
    intro N
    rw [← T_trunc h_add h_smul c N, ← h_add, trunc_add_tl]
  have hbound : ∀ N, ‖(∑ j ∈ Finset.range N, c j * dseq T j) - T c‖ ≤ C * h2Norm (tl c N) := by
    intro N
    have hbb := hb _ (mem_h2_tl hc N)
    rw [hsplitT N]
    simpa using hbb
  have hz : Tendsto (fun N => C * h2Norm (tl c N)) atTop (𝓝 0) := by
    simpa using (tendsto_h2Norm_tl hc).const_mul C
  have hdiff := squeeze_zero_norm hbound hz
  have hlim2 : Tendsto (fun N => ∑ j ∈ Finset.range N, c j * dseq T j) atTop (𝓝 (T c)) := by
    simpa using hdiff.add_const (T c)
  exact (tendsto_nhds_unique hlim2 hlim1)

end

end Melrose

open Melrose in
/-- **Riesz representation for the weighted space `h₂`.**
Every linear functional `T` on sequences that is bounded with respect to the
`h₂`-norm is represented by pairing against an element `d ∈ h₋₂`. -/
theorem melrose_sp2009_11
  (T : (ℕ → ℂ) → ℂ)
  (h_add : ∀ c₁ c₂, T (c₁ + c₂) = T c₁ + T c₂)
  (h_smul : ∀ (α : ℂ) c, T (α • c) = α * T c)
  (h_bdd : ∃ C : ℝ, 0 ≤ C ∧
    ∀ c, mem_h2 c → ‖T c‖ ≤ C * h2Norm c) :
  ∃ d : ℕ → ℂ, mem_hNeg2 d ∧
    ∀ c, mem_h2 c → T c = ∑' j : ℕ, c j * d j := by
  obtain ⟨C, hC, hb⟩ := h_bdd
  refine ⟨dseq T, dseq_mem_hNeg2 h_add h_smul hb, ?_⟩
  intro c hc
  exact repr_of_bdd h_add h_smul hb (dseq_mem_hNeg2 h_add h_smul hb) c hc

/-! ## `h_{±2}` are Hilbert spaces -/

namespace Melrose

/-- The weight defining `h₂`. -/
def h2Weight : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ 4

/-- The weight defining `h₋₂`. -/
noncomputable def hNeg2Weight : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ (-4 : ℝ)

lemma h2Weight_pos (j : ℕ) : 0 < h2Weight j := by
  rw [h2Weight]; positivity

lemma hNeg2Weight_pos (j : ℕ) : 0 < hNeg2Weight j :=
  Real.rpow_pos_of_pos (one_add_pos j) _

lemma mem_h2_iff : ∀ c, mem_h2 c ↔ memW h2Weight c := fun _ => Iff.rfl

lemma mem_hNeg2_iff : ∀ d, mem_hNeg2 d ↔ memW hNeg2Weight d := fun _ => Iff.rfl

lemma h2Norm_eq : ∀ c, h2Norm c = normW h2Weight c := fun _ => rfl

lemma hNeg2Norm_eq : ∀ d, hNeg2Norm d = normW hNeg2Weight d := fun _ => rfl

end Melrose

open Melrose in
/-- The `h₂`-norm satisfies the parallelogram law, so it is an inner product norm. -/
theorem h2_parallelogram {c c' : ℕ → ℂ} (hc : mem_h2 c) (hc' : mem_h2 c') :
    h2Norm (c + c') ^ 2 + h2Norm (c - c') ^ 2 = 2 * h2Norm c ^ 2 + 2 * h2Norm c' ^ 2 :=
  normW_parallelogram (fun j => (h2Weight_pos j).le) hc hc'

open Melrose in
/-- The `h₋₂`-norm satisfies the parallelogram law, so it is an inner product norm. -/
theorem hNeg2_parallelogram {d d' : ℕ → ℂ} (hd : mem_hNeg2 d) (hd' : mem_hNeg2 d') :
    hNeg2Norm (d + d') ^ 2 + hNeg2Norm (d - d') ^ 2
      = 2 * hNeg2Norm d ^ 2 + 2 * hNeg2Norm d' ^ 2 :=
  normW_parallelogram (fun j => (hNeg2Weight_pos j).le) hd hd'

open Melrose Filter Topology in
/-- **`h₂` is complete**: every sequence in `h₂` that is Cauchy for the `h₂`-norm converges
in that norm to an element of `h₂`. Together with `h2_parallelogram` this says that `h₂`
is a Hilbert space. -/
theorem h2_complete (u : ℕ → (ℕ → ℂ)) (hu : ∀ n, mem_h2 (u n))
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, h2Norm (u m - u n) < ε) :
    ∃ L : ℕ → ℂ, mem_h2 L ∧ Tendsto (fun n => h2Norm (u n - L)) atTop (𝓝 0) :=
  memW_complete h2Weight_pos u hu hcau

open Melrose Filter Topology in
/-- **`h₋₂` is complete**: every sequence in `h₋₂` that is Cauchy for the `h₋₂`-norm converges
in that norm to an element of `h₋₂`. Together with `hNeg2_parallelogram` this says that
`h₋₂` is a Hilbert space. -/
theorem hNeg2_complete (u : ℕ → (ℕ → ℂ)) (hu : ∀ n, mem_hNeg2 (u n))
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hNeg2Norm (u m - u n) < ε) :
    ∃ L : ℕ → ℂ, mem_hNeg2 L ∧ Tendsto (fun n => hNeg2Norm (u n - L)) atTop (𝓝 0) :=
  memW_complete hNeg2Weight_pos u hu hcau
