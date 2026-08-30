import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Melrose, Spring 2009, Problem 7

If `H` is a separable infinite-dimensional (complex) Hilbert space, then `H ⊕ H`, equipped with
the norm `(u₁, u₂) ↦ (‖u₁‖² + ‖u₂‖²)^(1/2)`, is a Hilbert space isometrically isomorphic to `H`.

In Mathlib the space "`H ⊕ H` with the above norm" is `WithLp 2 (H × H)` (the plain product
`H × H` carries the *sup* norm instead, which is not induced by an inner product; see
`melrose_sp2009_7_sup_norm_not_isometric` below).

The construction goes through Parseval/orthonormal expansions: a separable infinite-dimensional
Hilbert space has an orthonormal (Hilbert) basis indexed by `ℕ`, and so does `WithLp 2 (H × H)`;
comparing the two expansions gives the isometry.
-/

section Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two distinct members of an orthonormal set are at distance `√2 ≥ 1`. -/
theorem one_le_dist_of_orthonormal {w : Set E} (hw : Orthonormal ℂ ((↑) : w → E))
    {x y : E} (hx : x ∈ w) (hy : y ∈ w) (hxy : x ≠ y) : 1 ≤ dist x y := by
  have hxn : ‖x‖ = 1 := by
    simpa using hw.1 ⟨x, hx⟩
  have hyn : ‖y‖ = 1 := by
    simpa using hw.1 ⟨y, hy⟩
  have hinner : (inner ℂ x (-y) : ℂ) = 0 := by
    have : (inner ℂ x y : ℂ) = 0 :=
      hw.2 (show (⟨x, hx⟩ : w) ≠ ⟨y, hy⟩ by simpa [Subtype.ext_iff] using hxy)
    simpa [inner_neg_right] using this
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x (-y) hinner
  rw [← sub_eq_add_neg, norm_neg, hxn, hyn] at hpyth
  have hd : dist x y = ‖x - y‖ := dist_eq_norm x y
  nlinarith [norm_nonneg (x - y), hpyth, hd]

/-- An orthonormal set in a separable inner product space is countable. -/
theorem Set.Countable.of_orthonormal [TopologicalSpace.SeparableSpace E] {w : Set E}
    (hw : Orthonormal ℂ ((↑) : w → E)) : w.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun x => Metric.ball x (1 / 2))
    ?_ (fun i _ => Metric.isOpen_ball) (fun i _ => ⟨i, by simp⟩)
  intro x hx y hy hxy
  exact Metric.ball_disjoint_ball (by
    have := one_le_dist_of_orthonormal hw hx hy hxy
    linarith)

/-- A separable infinite-dimensional Hilbert space has a Hilbert basis indexed by `ℕ`. -/
theorem exists_hilbertBasis_nat (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] (h_inf : ¬ FiniteDimensional ℂ E) :
    Nonempty (HilbertBasis ℕ ℂ E) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ E
  have horth : Orthonormal ℂ ((↑) : w → E) := hb ▸ b.orthonormal
  have hcount : w.Countable := Set.Countable.of_orthonormal horth
  have hinf : w.Infinite := by
    rw [← Set.not_finite] at *
    intro hfin
    haveI := hfin.fintype
    exact h_inf (Module.Basis.finiteDimensional_of_finite b.toOrthonormalBasis.toBasis)
  haveI : Countable w := hcount.to_subtype
  haveI : Infinite w := hinf.to_subtype
  obtain ⟨d⟩ : Nonempty (Denumerable w) := nonempty_denumerable_iff.2 ⟨inferInstance, inferInstance⟩
  let e : ℕ ≃ w := (Denumerable.eqv w).symm
  refine ⟨HilbertBasis.mk (v := fun n => b (e n)) (b.orthonormal.comp e e.injective) ?_⟩
  have hrange : Set.range (fun n => b (e n)) = Set.range b := e.surjective.range_comp b
  rw [hrange, b.dense_span]

end Aux

/-- `WithLp 2 (H × H)` is infinite-dimensional if `H` is. -/
theorem not_finiteDimensional_prodLp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (h_inf : ¬ FiniteDimensional ℂ H) :
    ¬ FiniteDimensional ℂ (WithLp 2 (H × H)) := by
  intro hfin
  refine h_inf ?_
  have hsurj : Function.Surjective
      (((LinearMap.fst ℂ H H).comp (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap)) := by
    intro x
    exact ⟨WithLp.toLp 2 (x, 0), rfl⟩
  exact Module.Finite.of_surjective _ hsurj

/-
The originally proposed formalisation used the plain product `H × H`:

```
theorem melrose_sp2009_7
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (h_inf : ¬FiniteDimensional ℂ H) :
  ∃ (T : H ≃ₗᵢ[ℂ] H × H), ∀ u : H, ‖u‖ = ‖T u‖
```

This statement is **false**: in Mathlib `H × H` carries the sup norm `max ‖u₁‖ ‖u₂‖`, not the
norm `(‖u₁‖² + ‖u₂‖²)^(1/2)` of the problem, and the sup norm violates the parallelogram law,
so `H × H` is not isometrically isomorphic to any Hilbert space (see
`melrose_sp2009_7_sup_norm_not_isometric` below).  The faithful version of the problem uses the
`L²` product `WithLp 2 (H × H)`, and is proved next.
-/

/-- **Melrose, Spring 2009, Problem 7.**  For a separable infinite-dimensional complex Hilbert
space `H`, the direct sum `H ⊕ H` with the norm `(u₁, u₂) ↦ (‖u₁‖² + ‖u₂‖²)^(1/2)`
(i.e. `WithLp 2 (H × H)`) is a Hilbert space isometrically isomorphic to `H`. -/
theorem melrose_sp2009_7
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (h_inf : ¬ FiniteDimensional ℂ H) :
    ∃ T : H ≃ₗᵢ[ℂ] WithLp 2 (H × H), ∀ u : H, ‖u‖ = ‖T u‖ := by
  obtain ⟨bH⟩ := exists_hilbertBasis_nat H h_inf
  obtain ⟨bP⟩ := exists_hilbertBasis_nat (WithLp 2 (H × H)) (not_finiteDimensional_prodLp H h_inf)
  exact ⟨bH.repr.trans bP.repr.symm, fun u => ((bH.repr.trans bP.repr.symm).norm_map u).symm⟩

/-- The statement fails for the *plain* product `H × H`, which carries the sup norm: the sup norm
does not satisfy the parallelogram law, so no Hilbert space is isometrically isomorphic to it. -/
theorem melrose_sp2009_7_sup_norm_not_isometric
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] :
    IsEmpty (H ≃ₗᵢ[ℂ] H × H) := by
  constructor
  intro T
  obtain ⟨u, hu⟩ := exists_ne (0 : H)
  set x : H × H := (u, 0) with hx
  set y : H × H := (0, u) with hy
  have hxn : ‖x‖ = ‖u‖ := by simp [hx, Prod.norm_def]
  have hyn : ‖y‖ = ‖u‖ := by simp [hy, Prod.norm_def]
  have hadd : ‖x + y‖ = ‖u‖ := by simp [hx, hy, Prod.norm_def]
  have hsub : ‖x - y‖ = ‖u‖ := by simp [hx, hy, Prod.norm_def]
  -- transport the parallelogram law along the isometry
  have hpar : ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
      2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    have h1 := parallelogram_law_with_norm ℂ (T.symm x) (T.symm y)
    rw [show T.symm x + T.symm y = T.symm (x + y) from (T.symm.map_add x y).symm,
      show T.symm x - T.symm y = T.symm (x - y) from (T.symm.map_sub x y).symm,
      T.symm.norm_map, T.symm.norm_map, T.symm.norm_map, T.symm.norm_map] at h1
    exact h1
  rw [hxn, hyn, hadd, hsub] at hpar
  have : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
  exact hu (norm_eq_zero.mp this)
