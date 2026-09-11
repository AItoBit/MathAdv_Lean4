import Mathlib

structure ExactFiniteComplex
    (𝕜 : Type*) [Field 𝕜]
    (m : ℕ)
    (A : ℕ → Type*)
    [∀ k, AddCommGroup (A k)]
    [∀ k, Module 𝕜 (A k)] where
  d : ∀ k, A k →ₗ[𝕜] A (k + 1)
  exact_at_0 :
    LinearMap.ker (d 0) = ⊥
  exact_at_mid :
    ∀ k, k + 1 < m →
      LinearMap.range (d k) = LinearMap.ker (d (k + 1))
  exact_at_m :
    LinearMap.range (d (m - 1)) = ⊤

noncomputable def counterexampleComplex :
    ExactFiniteComplex ℝ 0 (fun _ : ℕ => ℝ) where
  d := fun _ => LinearMap.id
  exact_at_0 := by
    simp
  exact_at_mid := by
    intro k hk
    omega
  exact_at_m := by
    simp

theorem counterexample_dimension :
    (Module.finrank ℝ ℝ : ℤ) ≠ 0 := by
  norm_num
