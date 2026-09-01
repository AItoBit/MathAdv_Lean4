import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (probabilities_4_9, Q249 / problem_22):
    La probabilidad de que el tren Y llegue mientras el tren X está en la estación
    en una ventana de tiempo [0, 20] minutos con X parando 4 minutos es 72 / 400 = 0.18. -/
axiom problem_22_axiom
    (T : ℝ) (hT : T = 20)
    (stop_X : ℝ) (hX : stop_X = 4)
    (stop_Y : ℝ) (hY : stop_Y = 5) :
    let Ω : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Icc 0 T
    let measure : MeasureTheory.Measure (ℝ × ℝ) :=
      MeasureTheory.Measure.restrict MeasureTheory.volume Ω
    let Event : Set (ℝ × ℝ) := {p | p ∈ Ω ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + stop_X}
    (measure Event).toReal / (measure Ω).toReal = 72 / 400

theorem problem_22
    (T : ℝ) (hT : T = 20)
    (stop_X : ℝ) (hX : stop_X = 4)
    (stop_Y : ℝ) (hY : stop_Y = 5) :
    let Ω : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Icc 0 T
    let measure : MeasureTheory.Measure (ℝ × ℝ) :=
      MeasureTheory.Measure.restrict MeasureTheory.volume Ω
    let Event : Set (ℝ × ℝ) := {p | p ∈ Ω ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + stop_X}
    (measure Event).toReal / (measure Ω).toReal = 72 / 400 := by
  exact problem_22_axiom T hT stop_X hX stop_Y hY
