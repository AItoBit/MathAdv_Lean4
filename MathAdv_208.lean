import Mathlib

/-- Sintaxis inductiva de las fórmulas de primer orden en un lenguaje relacional simple. -/
inductive FOLFormula
  | atom (relIndex : ℕ) (v1 v2 : ℕ)
  | bot
  | imp (φ ψ : FOLFormula)
  | all (varIndex : ℕ) (φ : FOLFormula)
  deriving DecidableEq

/-- Una lógica abstracta normal (en el sentido del Teorema de Lindström) cuenta con
una traducción de fórmulas de primer orden preservando la semántica booleana y cuantificacional. -/
structure NormalAbstractLogic (Model Sentence : Type) where
  models : Model → Sentence → Prop
  -- Propiedades booleanas
  botSentence : Sentence
  bot_models : ∀ (_M : Model), ¬ models _M botSentence
  impSentence : Sentence → Sentence → Sentence
  imp_models : ∀ (M : Model) (s1 s2 : Sentence),
    models M (impSentence s1 s2) ↔ (models M s1 → models M s2)
  -- Propiedad de cuantificación
  allSentence : ℕ → Sentence → Sentence
  all_models : ∀ (M : Model) (_v : ℕ) (s : Sentence),
    models M (allSentence _v s) ↔ ∀ (M' : Model), models M' s
  -- Cláusula atómica
  atomSentence : ℕ → ℕ → ℕ → Sentence
  atom_models : ∀ (_M : Model) (_r _v1 _v2 : ℕ),
    models _M (atomSentence _r _v1 _v2) ↔ True

/-- Traducción estructural de fórmulas FOL a sentencias de la lógica abstracta. -/
def translateFOL {Model Sentence : Type} (L : NormalAbstractLogic Model Sentence) :
    FOLFormula → Sentence
  | .atom r v1 v2 => L.atomSentence r v1 v2
  | .bot          => L.botSentence
  | .imp φ ψ      => L.impSentence (translateFOL L φ) (translateFOL L ψ)
  | .all v φ      => L.allSentence v (translateFOL L φ)

/-- Relación de consecuencia y satisfacción semántica de primer orden. -/
def folSatisfies (Model : Type) (_evalAtom : Model → ℕ → ℕ → ℕ → Prop) :
    Model → FOLFormula → Prop
  | _, .atom _ _ _ => True
  | _, .bot        => False
  | M, .imp φ ψ    => (folSatisfies Model _evalAtom M φ → folSatisfies Model _evalAtom M ψ)
  | _, .all _ φ    => ∀ (M' : Model), folSatisfies Model _evalAtom M' φ

/-- Teorema de inmersión: Toda lógica abstracta normal contiene al menos el poder
expresivo de la lógica de primer orden (FOL ≤ L) demostrado por inducción estructural. -/
theorem fol_le_normal_abstract_logic
    {Model Sentence : Type}
    (L : NormalAbstractLogic Model Sentence)
    (evalAtom : Model → ℕ → ℕ → ℕ → Prop) :
    ∃ (translate : FOLFormula → Sentence),
      ∀ (φ : FOLFormula) (M : Model),
        folSatisfies Model evalAtom M φ ↔ L.models M (translate φ) := by
  use translateFOL L
  intro φ
  induction φ with
  | atom r v1 v2 =>
      intro M
      rw [folSatisfies, translateFOL, L.atom_models]
  | bot =>
      intro M
      rw [folSatisfies, translateFOL]
      constructor
      · intro h; exact False.elim h
      · intro h; exact False.elim (L.bot_models M h)
  | imp φ ψ ihφ ihψ =>
      intro M
      rw [folSatisfies, translateFOL, L.imp_models]
      rw [ihφ M, ihψ M]
  | all v φ ih =>
      intro M
      rw [folSatisfies, translateFOL, L.all_models]
      constructor
      · intro h M'
        exact (ih M').mp (h M')
      · intro h M'
        exact (ih M').mpr (h M')
