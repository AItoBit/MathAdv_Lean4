import Mathlib

open Equiv

/-- Definición: Un subgrupo tiene índice 3 en un grupo finito `G`. -/
def HasIndexThree {G : Type*} [Group G] [Fintype G] (H : Subgroup G) : Prop :=
  H.index = 3

/-- 
**Teorema (Gallian 11):**
Existe un subgrupo en `S₃` (el grupo de permutaciones de 3 elementos) 
de índice 3 que no es normal.
-/
theorem Gallian_11 :
    ∃ H : Subgroup (Equiv.Perm (Fin 3)),
      HasIndexThree (G := Equiv.Perm (Fin 3)) H ∧ ¬ H.Normal := by
  sorry
