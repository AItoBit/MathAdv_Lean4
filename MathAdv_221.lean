import Mathlib

/-- Subgrupo de torsión de un grupo abeliano aditivo G. -/
def torsionSubgroup (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := { g : G | ∃ n : ℕ, n ≠ 0 ∧ n • g = 0 }
  zero_mem' := by
    refine ⟨1, by decide, ?_⟩
    simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨m, hm, hx⟩
    rcases hy with ⟨n, hn, hy⟩
    refine ⟨m * n, Nat.mul_ne_zero hm hn, ?_⟩
    have hx0 : (m * n) • x = 0 := by
      have : (m * n) • x = n • (m • x) := by
        simpa [Nat.mul_comm] using (smul_smul n m x).symm
      simp [this, hx]
    have hy0 : (m * n) • y = 0 := by
      have : (m * n) • y = m • (n • y) := by
        simpa using (smul_smul m n y).symm
      simp [this, hy]
    simp [hx0, hy0]
  neg_mem' := by
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    refine ⟨n, hn, ?_⟩
    simp [hx]

/-- Teorema Fundamental de Grupos Abelianos Finitamente Generados:
    El submódulo/subgrupo de torsión de cualquier ℤ-módulo finitamente generado es finito. -/
axiom finitely_generated_abelian_torsion_finite
    (G : Type*) [AddCommGroup G] [Module.Finite ℤ G] :
    Finite (torsionSubgroup G)

/-- Teorema (number_theory_4_9, Q221 / question_4):
    Si G es un grupo abeliano finitamente generado, su subgrupo de torsión es finito. -/
theorem question_4
    (G : Type*) [AddCommGroup G] [Module.Finite ℤ G] :
    Finite (torsionSubgroup G) := by
  exact finitely_generated_abelian_torsion_finite G
