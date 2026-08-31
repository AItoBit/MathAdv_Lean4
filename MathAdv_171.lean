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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open scoped InnerProductSpace

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The orthogonal family produced by Gram-Schmidt from `v`. -/
noncomputable def w : Fin 3 → R3 :=
  ![
    (!₂[1, 2, 3] : R3),
    (!₂[(5 : ℝ) / 7, -(4 : ℝ) / 7, (1 : ℝ) / 7] : R3),
    (!₂[(1 : ℝ) / 3, (1 : ℝ) / 3, -(1 : ℝ) / 3] : R3)
  ]

/-- The original basis. -/
noncomputable def v : Fin 3 → R3 :=
  ![
    (!₂[1, 2, 3] : R3),
    (!₂[1, 0, 1] : R3),
    (!₂[1, 1, 1] : R3)
  ]

def OrthogonalFam (u : Fin 3 → R3) : Prop :=
  (∀ i, u i ≠ 0) ∧ ∀ i j, i ≠ j → ⟪u i, u j⟫_ℝ = 0

theorem w_orthogonal : OrthogonalFam w := by
  constructor
  · intro i hi
    have h0 := congrArg (fun z : R3 => z.ofLp 0) hi
    fin_cases i <;> simp [w] at h0
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [w, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num

theorem span_w_top : Submodule.span ℝ (Set.range w) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = ((x.ofLp 0 + 2 * x.ofLp 1 + 3 * x.ofLp 2) / 14) • w 0
      + ((5 * x.ofLp 0 - 4 * x.ofLp 1 + x.ofLp 2) / 6) • w 1
      + (x.ofLp 0 + x.ofLp 1 - x.ofLp 2) • w 2 := by
    ext i
    fin_cases i <;> simp [w] <;> ring
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem span_v_top : Submodule.span ℝ (Set.range v) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = ((x.ofLp 2 - x.ofLp 0) / 2) • v 0
      + ((x.ofLp 0 + x.ofLp 2) / 2 - x.ofLp 1) • v 1
      + (x.ofLp 0 + x.ofLp 1 - x.ofLp 2) • v 2 := by
    ext i
    fin_cases i <;> simp [v] <;> ring
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-! ### `w` is exactly the Gram-Schmidt orthogonalisation of `v` -/

theorem gramSchmidt_v_zero : InnerProductSpace.gramSchmidt ℝ v 0 = w 0 := by
  rw [InnerProductSpace.gramSchmidt_def, show (Finset.Iio (0 : Fin 3)) = ∅ from by decide]
  simp [v, w]

theorem norm_w_zero_sq : ‖(w 0)‖ ^ 2 = 14 := by
  simp [w, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [Real.sq_sqrt] <;> norm_num

theorem norm_w_one_sq : ‖(w 1)‖ ^ 2 = 6 / 7 := by
  simp [w, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [Real.sq_sqrt] <;> norm_num

theorem gramSchmidt_v_one : InnerProductSpace.gramSchmidt ℝ v 1 = w 1 := by
  rw [InnerProductSpace.gramSchmidt_def, show (Finset.Iio (1 : Fin 3)) = {0} from by decide]
  rw [Finset.sum_singleton, Submodule.starProjection_singleton, gramSchmidt_v_zero]
  have hi : ⟪w 0, v 1⟫_ℝ = 4 := by
    simp [w, v, PiLp.inner_apply, Fin.sum_univ_three]; norm_num
  rw [hi, norm_w_zero_sq]
  ext i
  fin_cases i <;> simp [v, w] <;> norm_num

theorem gramSchmidt_v_two : InnerProductSpace.gramSchmidt ℝ v 2 = w 2 := by
  rw [InnerProductSpace.gramSchmidt_def, show (Finset.Iio (2 : Fin 3)) = {0, 1} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Submodule.starProjection_singleton, Submodule.starProjection_singleton,
    gramSchmidt_v_zero, gramSchmidt_v_one]
  have hi0 : ⟪w 0, v 2⟫_ℝ = 6 := by
    simp [w, v, PiLp.inner_apply, Fin.sum_univ_three]; norm_num
  have hi1 : ⟪w 1, v 2⟫_ℝ = 2 / 7 := by
    simp [w, v, PiLp.inner_apply, Fin.sum_univ_three]; norm_num
  rw [hi0, hi1, norm_w_zero_sq, norm_w_one_sq]
  ext i
  fin_cases i <;> simp [v, w] <;> norm_num

/-- The family `w` is precisely the output of the Gram-Schmidt process applied to `v`. -/
theorem w_eq_gramSchmidt_v : w = InnerProductSpace.gramSchmidt ℝ v := by
  funext i
  fin_cases i
  · exact gramSchmidt_v_zero.symm
  · exact gramSchmidt_v_one.symm
  · exact gramSchmidt_v_two.symm

/-- `w` is an orthogonal family spanning all of `ℝ³`, hence an orthogonal basis,
and it spans the same subspace as the original family `v`. -/
theorem question_1 :
    OrthogonalFam w ∧
    Submodule.span ℝ (Set.range w) = ⊤ ∧
    Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) :=
  ⟨w_orthogonal, span_w_top, by rw [span_w_top, span_v_top]⟩
