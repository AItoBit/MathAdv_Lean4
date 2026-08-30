import Mathlib

/-!
# Rudin, Functional Analysis, Theorem 4.9 (Exercise 5.25 style)

`T ∈ B(X,Y)` is an isometry of `X` **onto** `Y` if and only if its adjoint `T*` is an
isometry of `Y*` **onto** `X*`.

Here `T* : Y* → X*` is the adjoint, characterized by `T* φ = φ ∘ T`, and the dual space
`X*` is `StrongDual ℝ X` (the space of continuous linear functionals with the operator norm).

The key ingredient is the Hahn–Banach theorem, used in two forms:
* `exists_dual_vector` (a norming functional exists for every nonzero vector), and
* `geometric_hahn_banach_closed_point` (separation of a closed subspace from an outside point),
  which shows that a proper closed subspace is annihilated by a nonzero functional.
-/

open scoped Classical

noncomputable section

namespace Rudin49

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section Basic

variable (T : X →L[ℝ] Y) (Tstar : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X)
  (hTstar : ∀ φ : StrongDual ℝ Y, Tstar φ = φ.comp T)

include hTstar

/-- Pointwise description of the adjoint. -/
lemma adjoint_apply (φ : StrongDual ℝ Y) (x : X) : Tstar φ x = φ (T x) := by
  rw [hTstar]; rfl

/-- If `T` is a surjective isometry, then `T*` preserves norms. -/
lemma norm_adjoint_eq_of_isometry_surjective
    (hT : ∀ x : X, ‖T x‖ = ‖x‖) (hsurj : Function.Surjective T) (φ : StrongDual ℝ Y) :
    ‖Tstar φ‖ = ‖φ‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjoint_apply T Tstar hTstar]
    calc ‖φ (T x)‖ ≤ ‖φ‖ * ‖T x‖ := φ.le_opNorm _
      _ = ‖φ‖ * ‖x‖ := by rw [hT]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← adjoint_apply T Tstar hTstar, hT]
    exact (Tstar φ).le_opNorm _

/-- If `T` is a bijective isometry, then `T*` is surjective. -/
lemma adjoint_surjective_of_isometry_surjective [CompleteSpace X] [CompleteSpace Y]
    (hT : ∀ x : X, ‖T x‖ = ‖x‖) (hsurj : Function.Surjective T) :
    Function.Surjective Tstar := by
  have hker : (T : X →ₗ[ℝ] Y).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have : ‖a - b‖ = 0 := by
      rw [← hT, map_sub]
      simpa using congrArg (fun z => ‖z - T b‖) hab
    simpa [sub_eq_zero] using this
  have hran : (T : X →ₗ[ℝ] Y).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : X ≃SL[RingHom.id ℝ] Y := ContinuousLinearEquiv.ofBijective T hker hran
  have he : ∀ x, e x = T x := fun _ => rfl
  intro ψ
  refine ⟨ψ.comp (e.symm : Y →L[ℝ] X), ?_⟩
  ext x
  rw [adjoint_apply T Tstar hTstar]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [← he x]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- If `T*` is a surjective isometry, then `T` preserves norms. -/
lemma norm_eq_of_adjoint_isometry_surjective
    (hTs : ∀ φ : StrongDual ℝ Y, ‖Tstar φ‖ = ‖φ‖) (hsurj : Function.Surjective Tstar)
    (x : X) : ‖T x‖ = ‖x‖ := by
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne ‖T x‖ 0 with h | h
    · rw [h]; exact norm_nonneg _
    · obtain ⟨φ, hφ1, hφ2⟩ := exists_dual_vector ℝ (T x) h
      have : ‖T x‖ = Tstar φ x := by rw [adjoint_apply T Tstar hTstar, hφ2]; norm_num
      calc ‖T x‖ = Tstar φ x := this
        _ ≤ ‖Tstar φ x‖ := le_abs_self _
        _ ≤ ‖Tstar φ‖ * ‖x‖ := (Tstar φ).le_opNorm _
        _ = ‖x‖ := by rw [hTs, hφ1, one_mul]
  · rcases eq_or_ne ‖x‖ 0 with h | h
    · rw [h]; exact norm_nonneg _
    · obtain ⟨ψ, hψ1, hψ2⟩ := exists_dual_vector ℝ x h
      obtain ⟨φ, rfl⟩ := hsurj ψ
      have hφ : ‖φ‖ = 1 := by rw [← hTs φ, hψ1]
      calc ‖x‖ = Tstar φ x := by rw [hψ2]; norm_num
        _ = φ (T x) := adjoint_apply T Tstar hTstar φ x
        _ ≤ ‖φ (T x)‖ := le_abs_self _
        _ ≤ ‖φ‖ * ‖T x‖ := φ.le_opNorm _
        _ = ‖T x‖ := by rw [hφ, one_mul]

end Basic

/-- Hahn–Banach separation: a proper closed subspace of a real normed space is annihilated
by a nonzero continuous linear functional. -/
lemma exists_dual_annihilating_of_closed_lt_top (M : Submodule ℝ Y) (hM : IsClosed (M : Set Y))
    {y : Y} (hy : y ∉ M) : ∃ φ : StrongDual ℝ Y, (∀ m ∈ M, φ m = 0) ∧ φ y ≠ 0 := by
  obtain ⟨f, u, hf, _hu⟩ :=
    geometric_hahn_banach_closed_point (s := (M : Set Y)) M.convex hM hy
  have hzero : ∀ m ∈ M, f m = 0 := by
    intro m hm
    by_contra hfm
    have hsmul : ((u + 1) / f m) • m ∈ M := M.smul_mem _ hm
    have := hf _ hsmul
    rw [map_smul] at this
    simp only [smul_eq_mul, div_mul_cancel₀ _ hfm] at this
    linarith
  refine ⟨f, hzero, ?_⟩
  have h0 : f 0 = 0 := map_zero f
  have : (0 : ℝ) < f y := by
    have := hf 0 M.zero_mem
    rw [h0] at this
    linarith
  exact ne_of_gt this

/-- If `T` is an isometry on a complete space `X`, its range is closed. -/
lemma isClosed_range_of_isometry [CompleteSpace X] (T : X →L[ℝ] Y)
    (hT : ∀ x : X, ‖T x‖ = ‖x‖) : IsClosed (Set.range T) := by
  have hiso : Isometry T := (AddMonoidHomClass.isometry_iff_norm T).mpr hT
  exact hiso.isUniformEmbedding.isUniformInducing.isComplete_range.isClosed

/-- If `T*` is injective and `T` is an isometry (with `X` complete), then `T` is surjective. -/
lemma surjective_of_adjoint_injective [CompleteSpace X]
    (T : X →L[ℝ] Y) (Tstar : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X)
    (hTstar : ∀ φ : StrongDual ℝ Y, Tstar φ = φ.comp T)
    (hinj : Function.Injective Tstar) (hT : ∀ x : X, ‖T x‖ = ‖x‖) :
    Function.Surjective T := by
  by_contra hns
  obtain ⟨y, hy⟩ := not_forall.mp hns
  have hyM : y ∉ (T : X →ₗ[ℝ] Y).range := by
    intro h
    exact hy (by simpa using h)
  have hclosed : IsClosed (((T : X →ₗ[ℝ] Y).range : Set Y)) := by
    have := isClosed_range_of_isometry T hT
    simpa [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using this
  obtain ⟨φ, hφ0, hφy⟩ :=
    exists_dual_annihilating_of_closed_lt_top (T : X →ₗ[ℝ] Y).range hclosed hyM
  have : Tstar φ = 0 := by
    ext x
    rw [adjoint_apply T Tstar hTstar]
    exact hφ0 _ ⟨x, rfl⟩
  have : φ = 0 := hinj (by simpa using this)
  exact hφy (by simp [this])

end Rudin49

open Rudin49 in
/-- **Rudin, Functional Analysis 4.9.** For Banach spaces `X`, `Y` and `T ∈ B(X,Y)` with adjoint
`T*` (given by `T* φ = φ ∘ T`), `T` is an isometry of `X` onto `Y` if and only if `T*` is an
isometry of `Y*` onto `X*`. (The dual space is written `StrongDual ℝ ·`.) -/
theorem rudin_5_25
    (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : X →L[ℝ] Y)
    (Tstar : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X)
    (hTstar_def : ∀ (φ : StrongDual ℝ Y), Tstar φ = φ.comp T) :
    (Isometry T ∧ LinearMap.range T.toLinearMap = ⊤) ↔
      (Isometry Tstar ∧ LinearMap.range Tstar.toLinearMap = ⊤) := by
  constructor
  · rintro ⟨hiso, hran⟩
    have hT : ∀ x : X, ‖T x‖ = ‖x‖ := (AddMonoidHomClass.isometry_iff_norm T).mp hiso
    have hsurj : Function.Surjective T := LinearMap.range_eq_top.mp hran
    refine ⟨(AddMonoidHomClass.isometry_iff_norm Tstar).mpr
      (norm_adjoint_eq_of_isometry_surjective T Tstar hTstar_def hT hsurj), ?_⟩
    exact LinearMap.range_eq_top.mpr
      (adjoint_surjective_of_isometry_surjective T Tstar hTstar_def hT hsurj)
  · rintro ⟨hiso, hran⟩
    have hTs : ∀ φ : StrongDual ℝ Y, ‖Tstar φ‖ = ‖φ‖ :=
      (AddMonoidHomClass.isometry_iff_norm Tstar).mp hiso
    have hsurj : Function.Surjective Tstar := LinearMap.range_eq_top.mp hran
    have hT : ∀ x : X, ‖T x‖ = ‖x‖ :=
      norm_eq_of_adjoint_isometry_surjective T Tstar hTstar_def hTs hsurj
    refine ⟨(AddMonoidHomClass.isometry_iff_norm T).mpr hT, ?_⟩
    exact LinearMap.range_eq_top.mpr
      (surjective_of_adjoint_injective T Tstar hTstar_def hiso.injective hT)

end
