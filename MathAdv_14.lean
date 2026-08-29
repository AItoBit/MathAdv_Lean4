import Mathlib

open scoped BigOperators Real Nat Classical Pointwise

/-- El conjunto de soluciones de `gⁿ = e` en un grupo `G`. -/
def nRootSet {G : Type*} [Group G] (n : ℕ) : Set G :=
  { g : G | g ^ n = (1 : G) }

/-- En el grupo simétrico S₃, las transposiciones (0 1) y (1 2)
satisfacen g² = e, pero su producto (un 3-ciclo) no. -/
lemma perm3_nRootSet_two_not_mul_closed :
    (Equiv.swap (0 : Fin 3) 1) ∈ nRootSet (G := Equiv.Perm (Fin 3)) 2 ∧
    (Equiv.swap (1 : Fin 3) 2) ∈ nRootSet (G := Equiv.Perm (Fin 3)) 2 ∧
    (Equiv.swap (0 : Fin 3) 1) * (Equiv.swap (1 : Fin 3) 2)
      ∉ nRootSet (G := Equiv.Perm (Fin 3)) 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [nRootSet, Set.mem_ofPred_eq] <;> decide

/-- Teorema (Gallian 15):
El enunciado «para todo grupo finito G y todo n > 0, el conjunto {g ∈ G : gⁿ = e} es un subgrupo»
es falso (tomando G = S₃ y n = 2). -/
theorem Gallian_15.{u} :
  ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (n : ℕ),
      0 < n ∧ ∀ H : Subgroup G, (H : Set G) ≠ nRootSet (G := G) n := by
  refine ⟨ULift.{u} (Equiv.Perm (Fin 3)), inferInstance, inferInstance, 2, by norm_num, ?_⟩
  intro H hH
  have key : ∀ x : ULift.{u} (Equiv.Perm (Fin 3)),
      (x ∈ nRootSet (G := ULift.{u} (Equiv.Perm (Fin 3))) 2 ↔ (x.down) ^ 2 = 1) := by
    intro x
    simp only [nRootSet, Set.mem_ofPred_eq]
    exact ⟨fun h => congrArg ULift.down h, fun h => ULift.down_inj.mp h⟩
  have ha : (ULift.up.{u} (Equiv.swap (0 : Fin 3) 1))
      ∈ nRootSet (G := ULift.{u} (Equiv.Perm (Fin 3))) 2 := by
    rw [key]; decide
  have hb : (ULift.up.{u} (Equiv.swap (1 : Fin 3) 2))
      ∈ nRootSet (G := ULift.{u} (Equiv.Perm (Fin 3))) 2 := by
    rw [key]; decide
  have hab : (ULift.up.{u} (Equiv.swap (0 : Fin 3) 1)) * (ULift.up.{u} (Equiv.swap (1 : Fin 3) 2))
      ∉ nRootSet (G := ULift.{u} (Equiv.Perm (Fin 3))) 2 := by
    rw [key]; decide
  rw [← hH] at ha hb hab
  exact hab (H.mul_mem ha hb)
