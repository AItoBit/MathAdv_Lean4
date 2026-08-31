import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
# Powers of the Kähler form are closed but not exact

Let `(M, g)` be a closed Kähler manifold of real dimension `2n` with Kähler form `ω`.
The classical argument is:

* `dω = 0`, hence every power `ω ^ k` is closed (Leibniz rule, `ω` has even degree `2`);
* `ω ^ n` is a nowhere vanishing top-degree form, proportional to the volume form, so
  `∫_M ω ^ n ≠ 0`;
* if `ω ^ k = dβ` for some `k ≤ n`, then `ω ^ n = ω ^ {n-k} ∧ dβ = d(ω ^ {n-k} ∧ β)`
  (again because `ω ^ {n-k}` is closed of even degree), and Stokes' theorem would give
  `∫_M ω ^ n = 0`, a contradiction;
* therefore `[ω ^ k] ≠ 0` in `H^{2k}(M; ℝ)` for `1 ≤ k ≤ n`, so all even cohomology groups
  in that range are nonzero.

Mathlib does not (yet) contain Kähler manifolds or de Rham cohomology of manifolds, so the
argument is formalized in the algebraic setting it really lives in: a graded algebra `𝒜`
over `ℝ` equipped with a differential `d` of degree `+1` satisfying the graded Leibniz rule,
together with an "integration" functional `I` on top degree `2n` that kills exact forms
(Stokes).  All the geometric input is packaged in the hypotheses of `KahlerData`; the
conclusions `KahlerData.pow_closed`, `KahlerData.pow_not_exact` and
`KahlerData.deRham_nontrivial` are exactly the statements of the problem.

The multiple-choice answer to the accompanying question is recorded in `correctReasoning`.
-/

namespace KahlerPowers

variable {A : Type*}

/-- Abstract data modelling the de Rham algebra of a closed Kähler manifold of real
dimension `2 * n`:

* `𝒜 i` is the space of `i`-forms inside the (associative, unital) `ℝ`-algebra `A`;
* `d` is the exterior derivative: it raises degree by one, squares to zero and satisfies
  the graded Leibniz rule;
* `I` is integration over the manifold; by Stokes' theorem it annihilates the exterior
  derivative of any `(2n-1)`-form;
* `omega` is the Kähler form: a closed `2`-form whose top power `ω ^ n` has nonzero
  integral (it is a positive multiple of the volume form). -/
structure KahlerData (A : Type*) [Ring A] [Algebra ℝ A] where
  /-- The space of `i`-forms. -/
  grading : ℕ → Submodule ℝ A
  /-- Products of forms respect degrees. -/
  gradedMonoid : SetLike.GradedMonoid grading
  /-- The exterior derivative. -/
  d : A →ₗ[ℝ] A
  /-- `d` raises the degree by one. -/
  d_mem : ∀ {i : ℕ} {x : A}, x ∈ grading i → d x ∈ grading (i + 1)
  /-- `d ∘ d = 0`. -/
  d_d : ∀ x : A, d (d x) = 0
  /-- The graded Leibniz rule. -/
  d_mul : ∀ {i j : ℕ} {x y : A}, x ∈ grading i → y ∈ grading j →
    d (x * y) = d x * y + ((-1 : ℝ) ^ i) • (x * d y)
  /-- Half the (real) dimension of the manifold. -/
  n : ℕ
  /-- Integration over the manifold. -/
  I : A →ₗ[ℝ] ℝ
  /-- Stokes' theorem: the integral of an exact top-degree form vanishes. -/
  stokes : ∀ {x : A}, x ∈ grading (2 * n - 1) → I (d x) = 0
  /-- The Kähler form. -/
  omega : A
  /-- The Kähler form is a `2`-form. -/
  omega_mem : omega ∈ grading 2
  /-- The Kähler form is closed. -/
  d_omega : d omega = 0
  /-- `ω ^ n` is (a positive multiple of) the volume form, so it has nonzero integral. -/
  I_omega_pow_ne_zero : I (omega ^ n) ≠ 0

namespace KahlerData

variable [Ring A] [Algebra ℝ A] (K : KahlerData A)

attribute [instance] KahlerData.gradedMonoid

/-- The constant function `1` is closed. -/
lemma d_one : K.d 1 = 0 := by
  have h1 : (1 : A) ∈ K.grading 0 := SetLike.one_mem_graded K.grading
  have h := K.d_mul h1 h1
  simp at h
  linear_combination (norm := module) h

/-- `ω ^ m` is a form of degree `2 * m`. -/
lemma omega_pow_mem (m : ℕ) : K.omega ^ m ∈ K.grading (2 * m) := by
  have := SetLike.pow_mem_graded (A := K.grading) m K.omega_mem
  simpa [smul_eq_mul, Nat.mul_comm] using this

/-- **All powers of the Kähler form are closed**, since `dω = 0` and `ω` has even degree. -/
lemma pow_closed (m : ℕ) : K.d (K.omega ^ m) = 0 := by
  induction m with
  | zero => simpa using K.d_one
  | succ m ih =>
      have h := K.d_mul (i := 2) (j := 2 * m) K.omega_mem (K.omega_pow_mem m)
      have : K.omega ^ (m + 1) = K.omega * K.omega ^ m := pow_succ' K.omega m
      rw [this, h, K.d_omega, ih]
      simp

/-- **No power `ω ^ k` with `1 ≤ k ≤ n` is exact.**  If `ω ^ k = dβ` with `β` of degree
`2k - 1`, then `ω ^ n = d (ω ^ (n - k) * β)` would be exact, forcing `∫ ω ^ n = 0`. -/
theorem pow_not_exact {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ K.n) :
    ¬ ∃ β ∈ K.grading (2 * k - 1), K.d β = K.omega ^ k := by
  rintro ⟨β, hβmem, hβ⟩
  have hpow : K.omega ^ (K.n - k) ∈ K.grading (2 * (K.n - k)) := K.omega_pow_mem _
  have hleib := K.d_mul hpow hβmem
  rw [K.pow_closed (K.n - k), hβ] at hleib
  have hsign : ((-1 : ℝ) ^ (2 * (K.n - k))) = 1 := by
    rw [pow_mul]; norm_num
  rw [hsign] at hleib
  have htop : K.omega ^ K.n = K.d (K.omega ^ (K.n - k) * β) := by
    rw [hleib]
    simp only [zero_mul, one_smul, zero_add]
    rw [← pow_add]
    congr 1
    omega
  have hmem : K.omega ^ (K.n - k) * β ∈ K.grading (2 * K.n - 1) := by
    have := SetLike.mul_mem_graded hpow hβmem
    have hdeg : 2 * (K.n - k) + (2 * k - 1) = 2 * K.n - 1 := by omega
    rwa [hdeg] at this
  exact K.I_omega_pow_ne_zero (by rw [htop]; exact K.stokes hmem)

/-- The closed forms of degree `i`. -/
def closedForms (i : ℕ) : Submodule ℝ A := K.grading i ⊓ LinearMap.ker K.d

/-- The exact forms of degree `i` (for `i ≥ 1`). -/
def exactForms (i : ℕ) : Submodule ℝ A := (K.grading (i - 1)).map K.d

/-- The `i`-th de Rham cohomology of the abstract de Rham algebra: closed `i`-forms modulo
exact ones. -/
def deRham (i : ℕ) : Type _ :=
  (K.closedForms i) ⧸ ((K.exactForms i).comap (K.closedForms i).subtype)

noncomputable instance (i : ℕ) : AddCommGroup (K.deRham i) := by
  unfold deRham; infer_instance

noncomputable instance (i : ℕ) : Module ℝ (K.deRham i) := by
  unfold deRham; infer_instance

/-- **The even cohomology groups do not vanish**: for `1 ≤ k ≤ n` the class of `ω ^ k` is a
nonzero element of `H^{2k}`. -/
theorem deRham_nontrivial {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ K.n) :
    Nontrivial (K.deRham (2 * k)) := by
  have hmem : K.omega ^ k ∈ K.closedForms (2 * k) :=
    ⟨K.omega_pow_mem k, K.pow_closed k⟩
  refine ⟨⟨Submodule.Quotient.mk ⟨K.omega ^ k, hmem⟩, 0, ?_⟩⟩
  intro hzero
  have hmem_exact : (⟨K.omega ^ k, hmem⟩ : K.closedForms (2 * k)) ∈
      (K.exactForms (2 * k)).comap (K.closedForms (2 * k)).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp hzero
  obtain ⟨β, hβmem, hβ⟩ : ∃ β ∈ K.grading (2 * k - 1), K.d β = K.omega ^ k := by
    rcases hmem_exact with ⟨β, hβmem, hβ⟩
    exact ⟨β, hβmem, hβ⟩
  exact K.pow_not_exact hk hkn ⟨β, hβmem, hβ⟩

end KahlerData

/-!
### Consistency of the axioms

The hypotheses collected in `KahlerData` are satisfiable with `n = 1`: the cohomology algebra
of the Riemann sphere `ℂP¹` (a closed Kähler surface) is `ℝ ⊕ ℝ·ω` with `ω ^ 2 = 0`, i.e. the
ring of dual numbers, graded with `1` in degree `0` and `ω` in degree `2`, with zero
differential and `I` the coefficient of `ω`.  So the theorems above are not vacuous.
-/

/-- The grading of the dual numbers modelling `H^•(ℂP¹; ℝ)`. -/
noncomputable def cpOneGrading : ℕ → Submodule ℝ (TrivSqZeroExt ℝ ℝ) := fun i =>
  if i = 0 then LinearMap.ker (TrivSqZeroExt.sndHom ℝ ℝ)
  else if i = 2 then LinearMap.ker (TrivSqZeroExt.fstHom ℝ ℝ ℝ).toLinearMap
  else ⊥

lemma cpOneGraded : SetLike.GradedMonoid cpOneGrading := by
  have : SetLike.GradedOne cpOneGrading := ⟨by simp [cpOneGrading, LinearMap.mem_ker]⟩
  have : SetLike.GradedMul cpOneGrading := ⟨by
    intro i j x y hx hy
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      by_cases hi2 : i = 2 <;> by_cases hj2 : j = 2 <;>
      simp_all [cpOneGrading, LinearMap.mem_ker, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.ext_iff]
    have hx0 : x = 0 := by rw [TrivSqZeroExt.ext_iff]; simp [hx.1, hx.2]
    simp [hx0]⟩
  exact ⟨⟩

/-- The axioms of `KahlerData` are consistent (with `n = 1`). -/
noncomputable def cpOne : KahlerData (TrivSqZeroExt ℝ ℝ) where
  grading := cpOneGrading
  gradedMonoid := cpOneGraded
  d := 0
  d_mem := by intro i x _; simp
  d_d := by simp
  d_mul := by intro i j x y _ _; simp
  n := 1
  I := TrivSqZeroExt.sndHom ℝ ℝ
  stokes := by simp
  omega := TrivSqZeroExt.inr 1
  omega_mem := by simp [cpOneGrading, LinearMap.mem_ker]
  d_omega := by simp
  I_omega_pow_ne_zero := by simp

/-- Concretely, the theorems apply to `cpOne`: `H^2 ≠ 0` there. -/
example : Nontrivial (cpOne.deRham 2) := by
  simpa using cpOne.deRham_nontrivial (k := 1) le_rfl le_rfl

/-- The four proposed lines of reasoning in the multiple-choice question. -/
inductive Reasoning
  /-- `ω ^ k` is the curvature form of a Hermitian line bundle. -/
  | curvatureForm
  /-- `ω ^ k` is closed; `ω ^ (dim M / 2)` is a nonzero multiple of the volume form, so it has
  nonzero integral and, by Stokes, cannot be exact. -/
  | stokesVolume
  /-- On a Kähler manifold all harmonic forms are parallel. -/
  | harmonicParallel
  /-- Apply Gauss–Bonnet. -/
  | gaussBonnet
  deriving DecidableEq, Repr

/-- The correct reasoning is (b): closedness from `dω = 0`, non-exactness from Stokes'
theorem together with `∫_M ω ^ (dim M / 2) ≠ 0`. -/
def correctReasoning : Reasoning := Reasoning.stokesVolume

end KahlerPowers
