import Mathlib

open Submodule Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- **The linear span of an infinite linearly independent sequence is never complete.**

If `x : ℕ → X` is a linearly independent sequence in a normed space `X`, then the
(not necessarily closed) linear span of its range, with the induced norm, is not a
complete space.

The proof uses the Baire category theorem: were the span complete, it would be a Baire
space, yet it is the countable union of the finite-dimensional subspaces spanned by the
initial segments `x 0, …, x (n-1)`.  Each of these is closed, and by linear independence
each is a proper subspace, hence has empty interior — contradicting Baire's theorem. -/
theorem bollobas_5_22
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : ℕ → X)
    (lin_indep : LinearIndependent ℝ x) :
    ¬CompleteSpace (Submodule.span ℝ (Set.range x)) := by
  intro hc
  set E := Submodule.span ℝ (Set.range x) with hE
  -- the sequence, viewed inside its own span
  set y : ℕ → E := fun i => ⟨x i, subset_span (mem_range_self i)⟩ with hy
  have hcomp : (E.subtype ∘ y) = x := rfl
  have hyli : LinearIndependent ℝ y :=
    LinearIndependent.of_comp E.subtype (by rw [hcomp]; exact lin_indep)
  -- the range of `y` spans all of `E`
  have hspan : Submodule.span ℝ (Set.range y) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := E.subtype) E.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, hcomp, Submodule.map_subtype_top, ← hE]
  -- the increasing family of finite-dimensional subspaces
  set S : ℕ → Submodule ℝ E := fun n => Submodule.span ℝ (y '' Set.Iio n) with hS
  have hfd : ∀ n, FiniteDimensional ℝ (S n) := fun n =>
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image y)
  have hclosed : ∀ n, IsClosed ((S n : Set E)) := fun n => by
    have := hfd n
    exact (S n).closed_of_finiteDimensional
  have hunion : (⋃ n, (S n : Set E)) = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    have hv : v ∈ Submodule.span ℝ (Set.range y) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hcv⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
    refine Set.mem_iUnion.2 ⟨c.support.sup id + 1, ?_⟩
    rw [← hcv]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_, rfl⟩)
    have : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
    exact Nat.lt_succ_of_le this
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  have htop : S n = ⊤ := Submodule.eq_top_of_nonempty_interior' (S n) hn
  have hmem : y n ∈ S n := htop ▸ Submodule.mem_top
  exact hyli.notMem_span_image (s := Set.Iio n) (by simp) hmem
