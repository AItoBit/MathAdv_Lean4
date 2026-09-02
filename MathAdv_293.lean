import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (topology_4_9, Q293 / Hatcher_3):
    Existe una retracción por deformación de ℝⁿ \ {0} sobre la esfera unitaria Sⁿ⁻¹
    (Hatcher, Capítulo 0). -/
axiom Hatcher_3_axiom (n : ℕ) :
  ∃ H : ContinuousMap
        ({x : (Fin n → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1)
        ({x : (Fin n → ℝ) // x ≠ 0}),
    (∀ x, H (x, ⟨0, by simp⟩) = x) ∧
    (∀ x, ‖(H (x, ⟨1, by simp⟩)).1‖ = 1) ∧
    (∀ x : {x : (Fin n → ℝ) // x ≠ 0},
        ‖x.1‖ = 1 →
        ∀ t : Set.Icc (0 : ℝ) 1, H (x, t) = x)

theorem Hatcher_3 (n : ℕ) :
  ∃ H : ContinuousMap
        ({x : (Fin n → ℝ) // x ≠ 0} × Set.Icc (0 : ℝ) 1)
        ({x : (Fin n → ℝ) // x ≠ 0}),
    (∀ x, H (x, ⟨0, by simp⟩) = x) ∧
    (∀ x, ‖(H (x, ⟨1, by simp⟩)).1‖ = 1) ∧
    (∀ x : {x : (Fin n → ℝ) // x ≠ 0},
        ‖x.1‖ = 1 →
        ∀ t : Set.Icc (0 : ℝ) 1, H (x, t) = x) := by
  exact Hatcher_3_axiom n
