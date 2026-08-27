import Mathlib

theorem Gallian_6 :
    ¬ ∃ H : Subgroup (↥(alternatingGroup (Fin 5))), Nat.card H = 30 := by
  rintro ⟨H, hH⟩
  -- 1. |A₅| = 60
  have hA5_card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide

  -- 2. By Lagrange's index formula, [A₅ : H] = 2
  have h_index : H.index = 2 := by
    have h_mul := H.card_mul_index
    rw [hA5_card, hH] at h_mul
    omega

  -- 3. A subgroup of index 2 is normal
  have h_normal : H.Normal := Subgroup.normal_of_index_eq_two h_index

  -- 4. A₅ is a simple group
  have h5 : 5 ≤ Nat.card (Fin 5) := by
    rw [Nat.card_eq_fintype_card]
    decide
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup h5

  -- 5. By simplicity, the normal subgroup H must be either ⊥ or ⊤
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H h_normal with hbot | htop
  · -- Case H = ⊥ (order is 1 ≠ 30)
    rw [hbot] at hH
    have : Nat.card ↥(⊥ : Subgroup ↥(alternatingGroup (Fin 5))) = 1 := Nat.card_unique
    omega
  · -- Case H = ⊤ (order is 60 ≠ 30)
    rw [htop] at hH
    have : Nat.card ↥(⊤ : Subgroup ↥(alternatingGroup (Fin 5))) = 60 := by
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hA5_card]
    omega
