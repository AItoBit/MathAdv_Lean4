import Mathlib

/-- Teorema (probabilities_4_9, Q236 / problem_9):
    La probabilidad de que el dígito 0 no aparezca entre k dígitos seleccionados
    de forma independiente y uniforme al azar en {0, ..., 9} es (9 / 10)^k. -/
theorem problem_9 (k : ℕ) :
    let all_seqs : Finset (Fin k → Fin 10) := Finset.univ
    let no_zero_seqs := all_seqs.filter (fun s => ∀ i, s i ≠ 0)
    (no_zero_seqs.card : ℝ) / all_seqs.card = (9 / 10 : ℝ) ^ k := by
  intro all_seqs no_zero_seqs
  -- 1) Cardinalidad de all_seqs = 10^k
  have h_all : all_seqs.card = 10 ^ k := by
    change (Finset.univ : Finset (Fin k → Fin 10)).card = 10 ^ k
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

  -- 2) Cardinalidad de no_zero_seqs = 9^k
  have h_nz : no_zero_seqs.card = 9 ^ k := by
    change (Finset.filter (fun s : Fin k → Fin 10 => ∀ i, s i ≠ 0) Finset.univ).card = 9 ^ k
    rw [← Fintype.card_subtype]
    have e_nz : {s : Fin k → Fin 10 // ∀ i, s i ≠ 0} ≃ (Fin k → {x : Fin 10 // x ≠ 0}) := {
      toFun := fun ⟨s, hs⟩ i => ⟨s i, hs i⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
      left_inv := fun ⟨s, hs⟩ => rfl
      right_inv := fun f => rfl
    }
    rw [Fintype.card_congr e_nz, Fintype.card_fun, Fintype.card_fin]
    have h_sub : Fintype.card {x : Fin 10 // x ≠ 0} = 9 := by
      decide
    rw [h_sub]

  -- 3) Sustitución y simplificación en ℝ
  rw [h_all, h_nz]
  push_cast
  rw [div_pow]
