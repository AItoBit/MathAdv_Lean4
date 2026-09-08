import Mathlib

/-- The subgroup of torsion elements (elements of finite order) of an additive
commutative group. -/
def torsionSubgroup (G : Type*) [AddCommGroup G] : AddSubgroup G :=
{ carrier := { g : G | ∃ n : ℕ, n ≠ 0 ∧ n • g = 0 }
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
    simp [hx] }

/-- The torsion subgroup, viewed as a `ℤ`-submodule. -/
def torsionSubmodule (G : Type*) [AddCommGroup G] : Submodule ℤ G :=
  AddSubgroup.toIntSubmodule (torsionSubgroup G)

/-- The torsion submodule of a finitely generated abelian group is finitely generated,
since `ℤ` is a Noetherian ring. -/
instance torsionSubmodule_finite (G : Type*) [AddCommGroup G] [Module.Finite ℤ G] :
    Module.Finite ℤ (torsionSubmodule G) := by
  have : IsNoetherian ℤ G := inferInstance
  infer_instance

/-- Every element of the torsion submodule is annihilated by a nonzero integer. -/
theorem torsionSubmodule_isTorsion (G : Type*) [AddCommGroup G] :
    Module.IsTorsion ℤ (torsionSubmodule G) := by
  rintro ⟨x, n, hn, hx⟩
  refine ⟨⟨(n : ℤ), ?_⟩, ?_⟩
  · simpa [mem_nonZeroDivisors_iff_ne_zero] using hn
  · ext
    simpa [natCast_zsmul] using hx

/-- The subgroup of elements of finite order in a finitely generated abelian group is
finite. -/
theorem question_4
  (G : Type*) [AddCommGroup G] [Module.Finite ℤ G] :
  Finite (torsionSubgroup G) :=
  Module.finite_of_fg_torsion (torsionSubmodule G) (torsionSubmodule_isTorsion G)

