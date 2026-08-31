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

set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- Complex `n`-space. -/
abbrev Cn (n : ℕ) := Fin n → ℂ

/-- The unit sphere `S^{2n-1} ⊆ ℂ^n`. -/
def sphere (n : ℕ) : Set (Cn n) := {z | ‖z‖ = 1}

/-- A vector field `X` is tangent to the sphere along the sphere if, at each point `z` of the
sphere, the squared distance to the origin has vanishing derivative in the direction `X z`. -/
def TangentAlongSphere (n : ℕ) (X : Cn n → Cn n) : Prop :=
  ∀ z, z ∈ sphere n →
    deriv (fun t : ℝ => ‖z + t • (X z)‖ ^ 2) 0 = 0

section Auxiliary

/-- Rewriting `z + t • (i z)` as the complex scalar `1 + it` acting on `z`. -/
private lemma smul_line_eq (n : ℕ) (z : Cn n) (t : ℝ) :
    z + t • ((Complex.I : ℂ) • z) = ((1 + t * Complex.I : ℂ)) • z := by
  rw [add_smul, one_smul, ← smul_assoc, Complex.real_smul]

private lemma norm_one_add_t_I_sq (t : ℝ) : ‖(1 + t * Complex.I : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

end Auxiliary

/-- **The infinitesimal generator of the rotation flow on the odd sphere.**

For `θ (t, z) = e^{it} z` on `S^{2n-1} ⊆ ℂ^n`, the flow is smooth, its infinitesimal generator
is `X z = i z`, which is a smooth vector field, tangent to the sphere along the sphere, and
nowhere vanishing on the sphere.

(The hypothesis `1 ≤ n` is part of the statement as given; the proof does not need it, since all
five conclusions also hold vacuously/trivially when `n = 0`.) -/
theorem Lee_9_4 (n : ℕ) (_hn : 1 ≤ n) :
  let θ : ℝ → Cn n → Cn n :=
    fun t z => (Complex.exp (Complex.I * t)) • z
  let X : Cn n → Cn n :=
    fun z => (Complex.I : ℂ) • z
  (ContDiff ℝ ⊤ (fun p : ℝ × Cn n => θ p.1 p.2)) ∧
  (ContDiff ℝ ⊤ X) ∧
  (∀ z, z ∈ sphere n → deriv (fun t => θ t z) 0 = X z) ∧
  (TangentAlongSphere n X) ∧
  (∀ z, z ∈ sphere n → X z ≠ 0) :=
by
  intro θ X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness of the flow
    have h1 : ContDiff ℝ ⊤ (fun p : ℝ × Cn n => Complex.exp (Complex.I * p.1)) :=
      (Complex.contDiff_exp (𝕜 := ℝ)).comp
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst))
    exact ContDiff.smul (𝕜' := ℂ) (F := Cn n) h1 contDiff_snd
  · -- smoothness of the generator
    exact ContDiff.const_smul _ contDiff_id
  · -- the generator is the `t`-derivative at `t = 0`
    intro z _
    have hg : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * t)) Complex.I 0 := by
      have h0 : HasDerivAt (fun t : ℝ => (Complex.I * t : ℂ)) Complex.I 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I)
      simpa using h0.cexp
    simpa [θ, X] using (hg.smul_const z).deriv
  · -- tangency along the sphere
    intro z _
    have key : (fun t : ℝ => ‖z + t • (X z)‖ ^ 2) = fun t : ℝ => (1 + t ^ 2) * ‖z‖ ^ 2 := by
      funext t
      rw [show X z = (Complex.I : ℂ) • z from rfl, smul_line_eq, norm_smul,
        mul_pow, norm_one_add_t_I_sq]
    rw [key]
    have : HasDerivAt (fun t : ℝ => (1 + t ^ 2) * ‖z‖ ^ 2) ((2 * 0 ^ 1) * ‖z‖ ^ 2) 0 := by
      simpa using (((hasDerivAt_pow 2 (0 : ℝ)).const_add 1).mul_const (‖z‖ ^ 2))
    rw [this.deriv]
    ring
  · -- nonvanishing on the sphere
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have : ‖z‖ = 1 := hz
      simp [h] at this
    exact smul_ne_zero Complex.I_ne_zero hz0
