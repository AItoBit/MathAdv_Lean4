import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Topology
open scoped InnerProductSpace

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

/-- If `⟪u n, e j⟫` converges for every basis vector `e j`, then `⟪u n, w⟫` converges for
every `w` in the linear span of the `e j`'s (no boundedness needed). -/
theorem tendsto_inner_of_mem_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ℕ → H) (e : ℕ → H)
    (h_converge : ∀ j : ℕ, ∃ c : ℂ,
      Filter.Tendsto (fun n : ℕ => (⟪u n, e j⟫_ℂ : ℂ)) Filter.atTop (𝓝 c)) :
    ∀ w ∈ Submodule.span ℂ (Set.range e), ∃ c : ℂ,
      Filter.Tendsto (fun n : ℕ => (⟪u n, w⟫_ℂ : ℂ)) Filter.atTop (𝓝 c) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact h_converge j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simpa [inner_add_right] using ha.add hb⟩
  | smul a x _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨a * c, by simpa [inner_smul_right] using hc.const_mul a⟩

/-- **Weak convergence criterion.**  If `‖u n‖` is bounded and `⟪u n, e j⟫` converges for each
element of an orthonormal basis `e`, then `⟪u n, v⟫` is Cauchy for every `v`, i.e. `u n`
converges weakly.  The key step is a three-term triangle inequality estimate.

The hypotheses are kept exactly as stated; the proof only uses the density of the span of `e`
(orthonormality, completeness and separability turn out not to be needed). -/
theorem melrose_sp2009_10
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H)
    (e : ℕ → H)
    (h_orthonormal : Orthonormal ℂ e)
    (h_dense : Dense (Submodule.span ℂ (Set.range e) : Set H))
    (h_bdd : ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C)
    (h_converge : ∀ j : ℕ, ∃ c : ℂ,
        Filter.Tendsto (fun n : ℕ => (⟪u n, e j⟫_ℂ : ℂ)) Filter.atTop (𝓝 c)) :
    ∀ v : H, CauchySeq (fun n : ℕ => (⟪u n, v⟫_ℂ : ℂ)) := by
  obtain ⟨C, hC⟩ := h_bdd
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hspan := tendsto_inner_of_mem_span u e h_converge
  intro v
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * (C + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.1 (h_dense v) δ hδ
  obtain ⟨c, hc⟩ := hspan w hw
  have hcauchy := hc.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 3) (by positivity)
  have hnorm : ‖v - w‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact hvw.le
  have key : ∀ k : ℕ, dist (⟪u k, v⟫_ℂ) (⟪u k, w⟫_ℂ) ≤ C * δ := by
    intro k
    rw [Complex.dist_eq, ← inner_sub_right]
    calc ‖(⟪u k, v - w⟫_ℂ : ℂ)‖ ≤ ‖u k‖ * ‖v - w‖ := norm_inner_le_norm _ _
      _ ≤ C * δ := mul_le_mul (hC k) hnorm (norm_nonneg _) hC0
  have hsmall : C * δ ≤ ε / 3 := by
    have heq : (C + 1) * δ = ε / 3 := by
      rw [hδdef]; field_simp
    nlinarith
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := key m
  have h2 := key n
  have h3 := hN m hm n hn
  have htri : dist (⟪u m, v⟫_ℂ) (⟪u n, v⟫_ℂ)
      ≤ dist (⟪u m, v⟫_ℂ) (⟪u m, w⟫_ℂ) + dist (⟪u m, w⟫_ℂ) (⟪u n, w⟫_ℂ)
        + dist (⟪u n, w⟫_ℂ) (⟪u n, v⟫_ℂ) := dist_triangle4 _ _ _ _
  rw [dist_comm (⟪u n, w⟫_ℂ) (⟪u n, v⟫_ℂ)] at htri
  linarith
