import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Marco abstracto para la codificación y reducción de una teoría indecidible
(Aritmética / Church-Tarski) hacia la teoría de anillos. -/
class IsRingTheoryEncoding
    (Lring : FirstOrder.Language)
    (RingTh : Lring.Theory)
    (code : Lring.Sentence → ℕ)
    (ProvableRing : Lring.Sentence → Prop) : Type _ where
  /-- Existe un predicado indecidible P sobre ℕ que no es computable. -/
  undecidable_pred : ℕ → Prop
  not_computable : ¬ ∃ (χP : ℕ → Bool), Computable χP ∧ ∀ n, χP n = true ↔ undecidable_pred n
  reduction_fn : ℕ → Lring.Sentence
  reduction_computable : Computable (fun n => code (reduction_fn n))
  reduction_correct : ∀ n, undecidable_pred n ↔ ProvableRing (reduction_fn n)

/-- Teorema (van den Dries, Lou, Q22):
    La teoría de anillos es indecidible. -/
theorem Dries_Lou_22
    (Lring : FirstOrder.Language)
    (RingTh : Lring.Theory)
    (code : Lring.Sentence → ℕ)
    (ProvableRing : Lring.Sentence → Prop)
    (h_enc : IsRingTheoryEncoding Lring RingTh code ProvableRing) :
    ¬ ∃ χ : ℕ → Bool, Computable χ ∧
        ∀ (phi : Lring.Sentence),
          χ (code phi) = true ↔ ProvableRing phi := by
  rintro ⟨χ, hχ_comp, hχ_dec⟩

  -- Extraemos los campos de la reducción
  have hP_not := h_enc.not_computable
  let f := h_enc.reduction_fn
  have hf_comp := h_enc.reduction_computable
  have hf_corr := h_enc.reduction_correct

  -- Componemos la supuesta función de decisión con la reducción
  let χP : ℕ → Bool := fun n => χ (code (f n))

  have hχP_comp : Computable χP :=
    hχ_comp.comp hf_comp

  have hχP_dec : ∀ n, χP n = true ↔ h_enc.undecidable_pred n := by
    intro n
    dsimp [χP]
    rw [hχ_dec (f n)]
    exact (hf_corr n).symm

  -- Llegamos a una contradicción con la indecidibilidad de undecidable_pred
  exact hP_not ⟨χP, hχP_comp, hχP_dec⟩
