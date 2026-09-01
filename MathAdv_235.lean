import Mathlib

/-- Teorema (probabilities_4_9, Q235 / problem_8):
    La probabilidad de que dos personas seleccionadas al azar compartan el mismo
    cumpleaños entre n días equiprobables es 1 / n. -/
theorem problem_8
    (n : ℕ) (hn : 0 < n) :
    let Ω := Fin n × Fin n
    let _same_birthday := {p : Ω | p.1 = p.2}
    ((Finset.univ.filter (fun p : Ω => p.1 = p.2)).card : ℝ) / (n : ℝ)^2 = 1 / (n : ℝ) := by
  intro Ω _same_birthday
  -- 1) Cardinalidad de la diagonal mediante equivalencia de tipos finitos
  have h_card : (Finset.univ.filter (fun p : Ω => p.1 = p.2)).card = n := by
    rw [← Fintype.card_subtype]
    have e : {p : Fin n × Fin n // p.1 = p.2} ≃ Fin n := {
      toFun := fun ⟨p, _⟩ => p.1
      invFun := fun i => ⟨(i, i), rfl⟩
      left_inv := fun ⟨⟨a, b⟩, (hab : a = b)⟩ => by
        subst hab
        rfl
      right_inv := fun _ => rfl
    }
    rw [Fintype.card_congr e]
    exact Fintype.card_fin n

  -- 2) Simplificación algebraica en ℝ
  rw [h_card]
  have hn_real_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hn
  field_simp [hn_real_ne]
  ring
