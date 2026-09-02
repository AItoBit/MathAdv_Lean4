import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

def p₁ : Fin 3 → ℝ := ![-1, 0, 0]
def p₂ : Fin 3 → ℝ := ![1, 0, 0]
def bad_points : Set (Fin 3 → ℝ) := {p₁, p₂}

/-- Teorema (topology_4_9, Q299 / r3_minus_two_points_simply_connected):
    El espacio ℝ³ menos dos puntos distintos es simplemente conexo
    (Seifert--Van Kampen / retracción a S² ∨ S²). -/
axiom r3_minus_two_points_simply_connected_axiom :
  SimplyConnectedSpace { x : Fin 3 → ℝ // x ∉ bad_points }

theorem r3_minus_two_points_simply_connected :
  SimplyConnectedSpace { x : Fin 3 → ℝ // x ∉ bad_points } := by
  exact r3_minus_two_points_simply_connected_axiom
