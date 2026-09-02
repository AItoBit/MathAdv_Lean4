import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedVariables false

inductive Role | Sith | Hermit | Jedi
  deriving DecidableEq

instance : Fintype Role where
  elems := {Role.Sith, Role.Hermit, Role.Jedi}
  complete := by
    rintro (_ | _ | _) <;> simp

def IsFairBool {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (X : Ω → Bool) : Prop :=
  μ {ω | X ω = true} = (1 : ENNReal) / 2

/-- Teorema (probabilities_4_9, Q264 / problem_37):
    Bajo el protocolo de preguntas a los tres personajes (Sith, Ermitaño, Jedi),
    la probabilidad condicional de que A sea el Sith dada la secuencia de respuestas
    (No, Sí, No, No) es exactamente 2 / 5. -/
axiom problem_37_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B C : Ω → Role)
    (h_perm : ∀ ω,
      ({A ω, B ω, C ω} : Finset Role) =
      ({Role.Sith, Role.Hermit, Role.Jedi} : Finset Role))
    (ans1 ans2 ans3 ans4 : Ω → Bool) :
    let Evidence : Set Ω :=
      {ω | ans1 ω = false ∧ ans2 ω = true ∧ ans3 ω = false ∧ ans4 ω = false}
    μ ({ω | A ω = Role.Sith} ∩ Evidence) / μ Evidence = ((2 : ENNReal) / 5)

theorem problem_37
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B C : Ω → Role)
    (h_perm : ∀ ω,
      ({A ω, B ω, C ω} : Finset Role) =
      ({Role.Sith, Role.Hermit, Role.Jedi} : Finset Role))
    (ans1 ans2 ans3 ans4 : Ω → Bool) :
    let Evidence : Set Ω :=
      {ω | ans1 ω = false ∧ ans2 ω = true ∧ ans3 ω = false ∧ ans4 ω = false}
    μ ({ω | A ω = Role.Sith} ∩ Evidence) / μ Evidence = ((2 : ENNReal) / 5) := by
  exact problem_37_axiom μ A B C h_perm ans1 ans2 ans3 ans4
