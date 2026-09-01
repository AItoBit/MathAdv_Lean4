import Mathlib

/-- Teorema (probabilities_4_9, Q230 / problem_3a):
    El número de configuraciones en Fin n → Bool donde todos los `true` (caras)
    ocurren al final es exactamente n + 1. -/
theorem problem_3a (n : ℕ) :
    ((Finset.range (n + 1)).image
        (fun k : ℕ => (fun i : Fin n => if i.val < k then false else true))).card
      = n + 1 := by
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range (n + 1)
  · intro k1 hk1 k2 hk2 h_eq
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    rcases lt_trichotomy k1 k2 with hlt | heq | hgt
    · have hk1_lt_n : k1 < n := by omega
      let i : Fin n := ⟨k1, hk1_lt_n⟩
      have h1 : (if i.val < k1 then false else true) = true := by
        simp [i]
      have h2 : (if i.val < k2 then false else true) = false := by
        simp [i, hlt]
      have h_eval := congr_fun h_eq i
      dsimp at h_eval
      rw [h1, h2] at h_eval
      contradiction
    · exact heq
    · have hk2_lt_n : k2 < n := by omega
      let i : Fin n := ⟨k2, hk2_lt_n⟩
      have h1 : (if i.val < k1 then false else true) = false := by
        simp [i, hgt]
      have h2 : (if i.val < k2 then false else true) = true := by
        simp [i]
      have h_eval := congr_fun h_eq i
      dsimp at h_eval
      rw [h1, h2] at h_eval
      contradiction
