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

/-!
# Closed manifolds of constant positive curvature in even dimensions

**Problem.** Show that in even dimensions the sphere `S^n` and the real projective space
`ℝP^n` are the only closed manifolds of constant positive curvature.

**Reasoning (multiple choice).** The correct line of argument is option (d): use the
classification of manifolds of constant sectional curvature (Killing–Hopf), identify the
universal cover with the round sphere `S^{2m}`, and analyse the finite groups acting freely
on `S^{2m}`.

Only the last, genuinely mathematical, step of that argument can currently be stated inside
Lean/Mathlib: Mathlib has no theory of sectional curvature, of space forms, or of the
Killing–Hopf classification, so the reduction "closed constant-positive-curvature manifold
`M` ⟹ `M = S^n / G` with `G` a group acting freely by isometries" cannot be formalised
here without inventing the whole underlying theory.

What *is* formalised below, and proved in full, is the even-dimensional group-theoretic
heart of the argument:

* `Geometry22.det_eq_one_or_neg_one_of_linearIsometryEquiv` — an orthogonal transformation
  has determinant `±1`;
* `Geometry22.exists_fixed_unit_of_det_one` — in odd ambient dimension (i.e. for a sphere of
  even dimension) an orthogonal transformation of determinant `1` fixes a unit vector, hence
  has a fixed point on the sphere;
* `Geometry22.card_le_two_of_freeAction_of_odd_finrank` and
  `Geometry22.card_le_two_of_free_action_on_even_sphere` — consequently any group acting
  freely by isometries on an even-dimensional sphere `S^{2m}` has at most two elements.

Since the universal cover of a closed manifold of constant positive curvature is `S^n` and
`M` is the quotient of `S^n` by the free isometric action of its deck transformation group
`G ≅ π₁(M)`, the last statement says that in even dimensions `G` is trivial or `ℤ/2`, i.e.
`M ≅ S^n` or `M ≅ ℝP^n`.
-/

namespace Geometry22

open Module

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant of the adjoint of a real endomorphism of a finite-dimensional inner
product space equals the determinant of the endomorphism (in an orthonormal basis the
adjoint is the transpose). -/
theorem det_adjoint_real (f : E →ₗ[ℝ] E) :
    LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  classical
  set v := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix v.toBasis f,
    ← LinearMap.det_toMatrix v.toBasis (LinearMap.adjoint f),
    LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
  simp

/-- The determinant of a linear isometry equivalence (an orthogonal transformation) is `±1`. -/
theorem det_eq_one_or_neg_one_of_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] E) :
    LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E)) = 1 ∨
      LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E)) = -1 := by
  have hadj : LinearMap.adjoint (f.toLinearEquiv : E →ₗ[ℝ] E)
      = (f.symm.toLinearEquiv : E →ₗ[ℝ] E) := f.adjoint_toLinearMap_eq_symm
  have hcomp : (f.toLinearEquiv : E →ₗ[ℝ] E)
      ∘ₗ LinearMap.adjoint (f.toLinearEquiv : E →ₗ[ℝ] E) = (1 : E →ₗ[ℝ] E) := by
    rw [hadj]; ext x; simp
  have hdet : LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E))
      * LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E)) = 1 := by
    have := congrArg LinearMap.det hcomp
    rwa [LinearMap.det_comp, det_adjoint_real, MonoidHom.map_one LinearMap.det] at this
  exact mul_self_eq_one_iff.mp hdet

/-- **Key even-dimensional fact.** If `E` is odd-dimensional and `f` is an orthogonal
transformation of `E` with determinant `1`, then `f` fixes a unit vector. Equivalently, an
orientation-preserving isometry of an even-dimensional sphere has a fixed point. -/
theorem exists_fixed_unit_of_det_one (f : E ≃ₗᵢ[ℝ] E) (hodd : Odd (finrank ℝ E))
    (hdet : LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E)) = 1) :
    ∃ x : E, ‖x‖ = 1 ∧ f x = x := by
  have hadj : LinearMap.adjoint (f.toLinearEquiv : E →ₗ[ℝ] E)
      = (f.symm.toLinearEquiv : E →ₗ[ℝ] E) := f.adjoint_toLinearMap_eq_symm
  have hadj1 : LinearMap.adjoint (1 : E →ₗ[ℝ] E) = 1 :=
    LinearMap.IsSymmetric.adjoint_eq fun _ => congrFun rfl
  have hmul : (f.toLinearEquiv : E →ₗ[ℝ] E)
      ∘ₗ ((1 : E →ₗ[ℝ] E) - LinearMap.adjoint (f.toLinearEquiv : E →ₗ[ℝ] E))
      = (f.toLinearEquiv : E →ₗ[ℝ] E) - 1 := by
    rw [hadj]; ext x; simp
  have hadjsub : LinearMap.adjoint ((1 : E →ₗ[ℝ] E) - (f.toLinearEquiv : E →ₗ[ℝ] E))
      = 1 - LinearMap.adjoint (f.toLinearEquiv : E →ₗ[ℝ] E) := by
    rw [map_sub, hadj1]
  have h1 : LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E) - 1)
      = LinearMap.det ((1 : E →ₗ[ℝ] E) - (f.toLinearEquiv : E →ₗ[ℝ] E)) := by
    rw [← hmul, LinearMap.det_comp, hdet, one_mul,
      ← det_adjoint_real ((1 : E →ₗ[ℝ] E) - (f.toLinearEquiv : E →ₗ[ℝ] E)), hadjsub]
  have h2 : LinearMap.det ((1 : E →ₗ[ℝ] E) - (f.toLinearEquiv : E →ₗ[ℝ] E))
      = -LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E) - 1) := by
    have h : (1 : E →ₗ[ℝ] E) - (f.toLinearEquiv : E →ₗ[ℝ] E)
        = (-1 : ℝ) • ((f.toLinearEquiv : E →ₗ[ℝ] E) - 1) := by ext x; simp
    rw [h, LinearMap.det_smul, hodd.neg_one_pow]; ring
  have hzero : LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E) - 1) = 0 := by
    linarith [h1.trans h2]
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at hzero
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
  have hfx : f x = x := by
    have h3 := LinearMap.mem_ker.mp hx
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
    simpa using h3
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul]
    simp [norm_ne_zero_iff.mpr hx0]
  · rw [map_smul, hfx]

omit [FiniteDimensional ℝ E] in
/-- Determinant of a product of orthogonal transformations. -/
theorem det_mul_linearIsometryEquiv (f g : E ≃ₗᵢ[ℝ] E) :
    LinearMap.det (((f * g).toLinearEquiv : E →ₗ[ℝ] E))
      = LinearMap.det ((f.toLinearEquiv : E →ₗ[ℝ] E))
        * LinearMap.det ((g.toLinearEquiv : E →ₗ[ℝ] E)) := by
  have h : ((f * g).toLinearEquiv : E →ₗ[ℝ] E)
      = (f.toLinearEquiv : E →ₗ[ℝ] E) ∘ₗ (g.toLinearEquiv : E →ₗ[ℝ] E) := by
    ext x; simp
  rw [h, LinearMap.det_comp]

/-- **Main algebraic result.** A group acting freely by linear isometries on the unit sphere
of an odd-dimensional real inner product space (i.e. on an even-dimensional sphere) has at
most two elements.

Together with the classification of space forms this says that a closed manifold of even
dimension `n` with constant positive curvature is the quotient of `S^n` by a group with at
most two elements, i.e. `S^n` itself or `ℝP^n`. -/
theorem card_le_two_of_freeAction_of_odd_finrank {G : Type*} [Group G]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (hodd : Odd (finrank ℝ E))
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E, ‖x‖ = 1 → rho g x ≠ x) :
    Nat.card G ≤ 2 := by
  classical
  set D : G → ℝ := fun g => LinearMap.det (((rho g).toLinearEquiv : E →ₗ[ℝ] E)) with hD
  have hD1 : D 1 = 1 := by
    have h : (((rho 1).toLinearEquiv : E →ₗ[ℝ] E)) = 1 := by
      rw [map_one]; ext x; simp
    show LinearMap.det (((rho 1).toLinearEquiv : E →ₗ[ℝ] E)) = 1
    rw [h, MonoidHom.map_one LinearMap.det]
  have hDmul : ∀ g h : G, D (g * h) = D g * D h := by
    intro g h
    simp only [hD, map_mul]
    exact det_mul_linearIsometryEquiv _ _
  -- every non-identity element acts by an orientation-reversing isometry
  have hDneg : ∀ g : G, g ≠ 1 → D g = -1 := by
    intro g hg
    rcases det_eq_one_or_neg_one_of_linearIsometryEquiv (rho g) with h | h
    · obtain ⟨x, hx, hfx⟩ := exists_fixed_unit_of_det_one (rho g) hodd h
      exact absurd hfx (hfree g hg x hx)
    · exact h
  -- hence there is at most one non-identity element
  have key : ∀ g h : G, g ≠ 1 → h ≠ 1 → g = h := by
    intro g h hg hh
    by_contra hgh
    have hne : g * h⁻¹ ≠ 1 := by
      intro hc
      exact hgh (by simpa using congrArg (fun z => z * h) hc)
    have hinv : D h⁻¹ = -1 := by
      have := hDmul h h⁻¹
      rw [mul_inv_cancel, hD1, hDneg h hh] at this
      linarith
    have h1 : D (g * h⁻¹) = 1 := by
      rw [hDmul, hDneg g hg, hinv]; ring
    have h2 : D (g * h⁻¹) = -1 := hDneg _ hne
    rw [h1] at h2
    norm_num at h2
  have hinj : Function.Injective (fun g : G => decide (g = 1)) := by
    intro a b hab
    simp only [decide_eq_decide] at hab
    by_cases ha : a = 1
    · rw [ha, hab.mp ha]
    · exact key a b ha fun hb => ha (hab.mpr hb)
  have : Finite G := Finite.of_injective _ hinj
  simpa using Nat.card_le_card_of_injective _ hinj

end InnerProduct

/-- **Even-dimensional sphere version.** Let `n` be even and let a group `G` act on the
Euclidean space `ℝ^{n+1}` by linear isometries so that the action on the unit sphere `S^n`
is free. Then `G` has at most two elements — so the quotient `S^n / G` is either `S^n` or
`ℝP^n`. -/
theorem card_le_two_of_free_action_on_even_sphere {n : ℕ} (hn : Even n) {G : Type*} [Group G]
    (rho : G →* (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
    (hfree : ∀ g : G, g ≠ 1 → ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      rho g x ≠ x) :
    Nat.card G ≤ 2 := by
  refine card_le_two_of_freeAction_of_odd_finrank rho ?_ ?_
  · simpa [finrank_euclideanSpace] using Even.add_one hn
  · intro g hg x hx
    exact hfree g hg x (by simpa [mem_sphere_iff_norm] using hx)

/-- The list of proposed lines of reasoning for the problem. -/
inductive Reasoning
  | hadamard          -- (a) Apply Hadamard's theorem.
  | stokes            -- (b) Use Stokes' theorem and total curvature.
  | gaussBonnet       -- (c) Apply Gauss–Bonnet to compute the Euler characteristic.
  | spaceForms        -- (d) Classification of constant curvature manifolds + free actions
  deriving DecidableEq

/-- The correct reasoning is (d): classify constant curvature manifolds, identify the
universal cover with `S^{2m}`, and analyse the finite groups acting freely in even
dimensions. -/
def correctReasoning : Reasoning := Reasoning.spaceForms

end Geometry22

/-
The statement as originally proposed is reproduced here for reference.  It is deliberately
left commented out: `HasConstantPositiveCurvature` and `IsDiffeomorphic` are introduced as
`opaque` constants, i.e. predicates whose meaning is hidden from the logic, and the charted
space / manifold structures on `RealProjectiveSpace` are `sorry`-ed.  With opaque hypotheses
and an opaque conclusion the statement carries no mathematical content: it is neither
provable nor refutable, since nothing at all is known about the two predicates.  The
mathematical content of the problem that can be expressed with the currently available
theory is proved above.

opaque RealProjectiveSpace (n : ℕ) : Type*
instance (n : ℕ) : TopologicalSpace (RealProjectiveSpace n) := sorry
instance (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (RealProjectiveSpace n) := sorry
instance (n : ℕ) :
    SmoothManifoldWithCorners
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (RealProjectiveSpace n) := sorry

opaque HasConstantPositiveCurvature
  (n : ℕ) (M : Type*)
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop

opaque IsDiffeomorphic
  (n : ℕ) (M N : Type*)
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
  [SmoothManifoldWithCorners
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) N] : Prop

theorem geometry_22
  (n : ℕ) (M : Type*)
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [SmoothManifoldWithCorners
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
  [CompactSpace M]
  [Fact (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1)]
  (h_even : Even n)
  (h_curv : HasConstantPositiveCurvature n M) :
  IsDiffeomorphic n M (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∨
  IsDiffeomorphic n M (RealProjectiveSpace n) := by
  sorry
-/
