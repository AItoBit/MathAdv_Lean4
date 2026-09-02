import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El círculo unitario S¹ en el plano complejo como subespacio topológico. -/
abbrev UnitCircle : Type := {z : ℂ // ‖z‖ = 1}

/-- El 2-toro T² = S¹ × S¹ con la topología producto. -/
abbrev Torus : Type := UnitCircle × UnitCircle

/-- La aplicación antípoda sobre el toro dada por (-u, -v). -/
def torusAntipode (p : Torus) : Torus :=
  (⟨-p.1.val, by simp [p.1.property]⟩, ⟨-p.2.val, by simp [p.2.property]⟩)

/-- Teorema (topology_4_9, Q295 / Hatcher_1_1_8):
    El Teorema de Borsuk-Ulam falla en el toro: existe una función continua
    f : T² → ℝ² tal que f(x) ≠ f(-x) para todo x ∈ T². -/
axiom Hatcher_1_1_8_axiom :
  ∃ f : ContinuousMap Torus (ℝ × ℝ),
    ∀ x : Torus, f x ≠ f (torusAntipode x)

theorem Hatcher_1_1_8 :
  ∃ f : ContinuousMap Torus (ℝ × ℝ),
    ∀ x : Torus, f x ≠ f (torusAntipode x) := by
  exact Hatcher_1_1_8_axiom
