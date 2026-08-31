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

universe u v

/-! ## Abstract form of the statement

A `1`-form is modelled as an assignment of a value in `V` to each point of `M`, the
differential is modelled as an abstract map `d` from a type `F` of "functions" to
`1`-forms, and the key analytic input (on a compact manifold, the differential of any
function vanishes somewhere, namely at a maximum) is the hypothesis `has_zero`. -/

abbrev MyOneForm (M : Type u) (V : Type v) : Type (max u v) := M → V

def MyNowhereVanishing {M : Type u} {V : Type v} [Zero V] (ω : MyOneForm M V) : Prop :=
  ∀ x : M, ω x ≠ 0

def MyExact {M : Type u} {F : Type*} {V : Type v} (d : F → MyOneForm M V) (ω : MyOneForm M V) :
    Prop :=
  ∃ f : F, d f = ω

/-- A nowhere vanishing `1`-form on a compact manifold cannot be exact: if `ω = d f` then,
since the differential of every function vanishes at some point (a maximum of `f`), `ω`
would vanish there too. -/
theorem Tu_24_1
  {M : Type u} [TopologicalSpace M] [CompactSpace M]
  {F : Type*} {V : Type v} [Zero V]
  (d : F → MyOneForm M V)
  (has_zero : ∀ f : F, ∃ x : M, d f x = 0)
  (ω : MyOneForm M V)
  (h_nv : MyNowhereVanishing ω) :
  ¬ MyExact d ω :=
by
  rintro ⟨f, rfl⟩
  obtain ⟨x, hx⟩ := has_zero f
  exact h_nv x hx

/-! ## Concrete differential-geometric version

We now carry out the same argument for genuine smooth manifolds: a nowhere vanishing
`1`-form on a nonempty compact boundaryless smooth manifold is not the differential of
any (differentiable) function. -/

section Manifold

open Manifold Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- At a global maximum, the differential of a differentiable real function on a
boundaryless manifold vanishes. -/
theorem mfderiv_eq_zero_of_isMax {f : M → ℝ} {x : M} (hmax : ∀ y : M, f y ≤ f x)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  have h2 := hd.hasMFDerivAt.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h2
  have hlm : IsLocalMax (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) ((extChartAt I x) x) := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq]
    rw [extChartAt_to_inv]
    exact hmax _
  exact hlm.hasFDerivAt_eq_zero h2

/-- On a nonempty compact boundaryless manifold, the differential of any differentiable
real valued function vanishes at some point. -/
theorem exists_mfderiv_eq_zero [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (hd : MDifferentiable I 𝓘(ℝ, ℝ) f) :
    ∃ x : M, mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  obtain ⟨x, -, hx⟩ :=
    isCompact_univ.exists_isMaxOn (s := (univ : Set M)) univ_nonempty
      hd.continuous.continuousOn
  exact ⟨x, mfderiv_eq_zero_of_isMax (fun y => hx (mem_univ y)) (hd x)⟩

/-- **A nowhere vanishing `1`-form on a compact manifold is not exact.** Here a `1`-form is
a (not necessarily continuous) section `ω` of the cotangent bundle, and exactness means
`ω = df` for some differentiable function `f : M → ℝ`. -/
theorem nowhere_vanishing_one_form_not_exact [CompactSpace M] [Nonempty M]
    (ω : ∀ x : M, TangentSpace I x →L[ℝ] ℝ) (h_nv : ∀ x : M, ω x ≠ 0) :
    ¬ ∃ f : M → ℝ, MDifferentiable I 𝓘(ℝ, ℝ) f ∧ ∀ x : M, mfderiv I 𝓘(ℝ, ℝ) f x = ω x := by
  rintro ⟨f, hf, hfω⟩
  obtain ⟨x, hx⟩ := exists_mfderiv_eq_zero hf
  exact h_nv x (by rw [← hfω x, hx]; rfl)

end Manifold
