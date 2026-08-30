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
# Two Banach norms on the same vector space

If a real vector space `V` is complete with respect to each of two norms, then the two
induced topologies are either equal ("equivalent") or incomparable: it is impossible for
one to be strictly finer than the other.

The proof is an application of the open mapping theorem: if one topology is finer than the
other, the identity map is a continuous linear bijection between two Banach spaces, hence
an isomorphism, so the two topologies coincide.
-/

section TwoNorms

variable {V : Type*}

/-- The uniform structure on `V` induced by a norm `p` (a homogeneous `AddGroupNorm`). -/
@[instance_reducible]
noncomputable def normUniformity [AddCommGroup V] (p : AddGroupNorm V) : UniformSpace V :=
  (p.toNormedAddCommGroup).toUniformSpace

/-- The topology on `V` induced by the norm `p`. -/
@[instance_reducible]
noncomputable def normTopology [AddCommGroup V] (p : AddGroupNorm V) : TopologicalSpace V :=
  (normUniformity p).toTopologicalSpace

/-- `V` is a Banach space for the norm `p`: it is complete for the uniformity induced by `p`. -/
def IsBanachNorm [AddCommGroup V] (p : AddGroupNorm V) : Prop :=
  @CompleteSpace V (normUniformity p)

/-- Absolute homogeneity of `p` with respect to real scalars: `p (c • x) = |c| * p x`.
Together with the `AddGroupNorm` axioms this says that `p` is a norm on the real vector
space `V`. -/
def IsHomogeneousNorm [AddCommGroup V] [Module ℝ V] (p : AddGroupNorm V) : Prop :=
  ∀ (c : ℝ) (x : V), p (c • x) = |c| * p x

/-- A homogeneous `AddGroupNorm` on a real vector space makes it a normed space. -/
@[instance_reducible]
noncomputable def normedSpaceOfHomogeneous [AddCommGroup V] [Module ℝ V] (p : AddGroupNorm V)
    (hp : IsHomogeneousNorm p) :
    @NormedSpace ℝ V _ (p.toNormedAddCommGroup).toSeminormedAddCommGroup := by
  letI : NormedAddCommGroup V := p.toNormedAddCommGroup
  exact { (inferInstance : Module ℝ V) with
    norm_smul_le := by
      intro a b
      show p (a • b) ≤ ‖a‖ * p b
      rw [hp]
      exact le_of_eq rfl }

/-- Open mapping theorem, in the form: a continuous linear equivalence between Banach spaces
has continuous inverse. -/
theorem continuous_symm_of_continuous_linearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (e : E ≃ₗ[ℝ] F)
    (he : Continuous e) : Continuous e.symm := by
  let f : E →L[ℝ] F := ⟨e.toLinearMap, he⟩
  have hker : (f : E →ₗ[ℝ] F).ker = ⊥ := LinearMap.ker_eq_bot_of_injective e.injective
  have hrange : (f : E →ₗ[ℝ] F).range = ⊤ := LinearMap.range_eq_top_of_surjective _ e.surjective
  refine ((ContinuousLinearEquiv.ofBijective f hker hrange).symm.continuous).congr ?_
  intro y
  apply e.injective
  rw [e.apply_symm_apply]
  exact (ContinuousLinearEquiv.ofBijective f hker hrange).apply_symm_apply y

/-- If `V` is a Banach space for two norms and one of the induced topologies is finer than
the other, then the two topologies are equal. -/
theorem normTopology_eq_of_le [AddCommGroup V] [Module ℝ V]
    (p₁ p₂ : AddGroupNorm V)
    (hp₁ : IsHomogeneousNorm p₁) (hp₂ : IsHomogeneousNorm p₂)
    (hb₁ : IsBanachNorm p₁) (hb₂ : IsBanachNorm p₂)
    (h : normTopology p₁ ≤ normTopology p₂) : normTopology p₁ = normTopology p₂ := by
  have hcont : @Continuous V V (normTopology p₁) (normTopology p₂) id :=
    continuous_id_iff_le.mpr h
  have key := @continuous_symm_of_continuous_linearEquiv V V
      p₁.toNormedAddCommGroup (normedSpaceOfHomogeneous p₁ hp₁) hb₁
      p₂.toNormedAddCommGroup (normedSpaceOfHomogeneous p₂ hp₂) hb₂ (LinearEquiv.refl ℝ V) hcont
  have key' : @Continuous V V (normTopology p₂) (normTopology p₁) id := key
  exact le_antisymm h (continuous_id_iff_le.mp key')

/-- **Two Banach norms on the same vector space.**
If a real vector space `V` is complete with respect to each of two norms `p₁`, `p₂`, then
the topologies they induce are either equal or incomparable. -/
theorem banach_two_norms_topologies_eq_or_incomparable [AddCommGroup V] [Module ℝ V]
    (p₁ p₂ : AddGroupNorm V)
    (hp₁ : IsHomogeneousNorm p₁) (hp₂ : IsHomogeneousNorm p₂)
    (hb₁ : IsBanachNorm p₁) (hb₂ : IsBanachNorm p₂) :
    normTopology p₁ = normTopology p₂ ∨
      (¬ normTopology p₁ ≤ normTopology p₂ ∧ ¬ normTopology p₂ ≤ normTopology p₁) := by
  by_cases h : normTopology p₁ ≤ normTopology p₂
  · exact Or.inl (normTopology_eq_of_le p₁ p₂ hp₁ hp₂ hb₁ hb₂ h)
  · by_cases h' : normTopology p₂ ≤ normTopology p₁
    · exact Or.inl (normTopology_eq_of_le p₂ p₁ hp₂ hp₁ hb₂ hb₁ h').symm
    · exact Or.inr ⟨h, h'⟩

/-- Without any hypothesis linking the topologies to complete norms, the conclusion fails:
on `ℝ` the discrete and the indiscrete topologies are comparable and distinct. -/
theorem exists_comparable_distinct_topologies :
    ¬ (∀ (T₁ T₂ : TopologicalSpace ℝ), T₁ = T₂ ∨ (¬ T₁ ≤ T₂ ∧ ¬ T₂ ≤ T₁)) := by
  intro h
  rcases h ⊥ ⊤ with h1 | ⟨h2, _⟩
  · have hop : @IsOpen ℝ ⊥ {(0 : ℝ)} := trivial
    rw [h1] at hop
    rcases (TopologicalSpace.isOpen_top_iff _).mp hop with he | he
    · have : (0 : ℝ) ∈ (∅ : Set ℝ) := he ▸ Set.mem_singleton (0 : ℝ)
      simp at this
    · have : (1 : ℝ) ∈ ({0} : Set ℝ) := he ▸ Set.mem_univ (1 : ℝ)
      simp at this
  · exact h2 bot_le

end TwoNorms
