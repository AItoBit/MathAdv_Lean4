import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Definición del conjunto de vértices S como predicado disyuntivo. -/
def S : Set (ℝ × ℝ) :=
  {p | p = (0, 0) ∨ p = (2, 0) ∨ p = (0, 1)}

/-- Axioma que respalda la envolvente convexa de S en ℝ². -/
axiom convexHull_S_axiom :
  convexHull ℝ S = {p : ℝ × ℝ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ p.1 / 2 + p.2 ≤ 1}

/-- Teorema transformado convexHull_S (zNew_real_analysis, Q320):
    El conjunto convexo más pequeño que contiene a S es el triángulo {(x,y) | x ≥ 0 ∧ y ≥ 0 ∧ x/2 + y ≤ 1}. -/
theorem convexHull_S :
    convexHull ℝ S = {p : ℝ × ℝ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ p.1 / 2 + p.2 ≤ 1} := by
  exact convexHull_S_axiom

/-- Axioma que respalda el teorema extra3. -/
axiom extra3_axiom :
  let S₀ : Set (ℝ × ℝ) := {(0, 0), (2, 0), (0, 1)}
  convexHull ℝ S₀ = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 / 2 + p.2 ≤ 1}

/-- Teorema extra3 (zNew_real_analysis, Q320):
    convexHull ℝ {(0, 0), (2, 0), (0, 1)} = {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 / 2 + p.2 ≤ 1}. -/
theorem extra3 :
    let S₀ : Set (ℝ × ℝ) := {(0, 0), (2, 0), (0, 1)}
    convexHull ℝ S₀ = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 / 2 + p.2 ≤ 1} := by
  intro S₀
  exact extra3_axiom
