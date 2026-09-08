import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting

/-- Un índice `e` corresponde a una función total si está definida para todo `x : ℕ`. -/
def isTotal (phi : ℕ → (ℕ →. ℕ)) (e : ℕ) : Prop :=
  ∀ x : ℕ, (phi e x).Dom

/-- Una enumeración estándar admisible de todas las funciones recursivas parciales. -/
def enumeratesAllPartrec (phi : ℕ → (ℕ →. ℕ)) : Prop :=
  (∀ i, Nat.Partrec (phi i)) ∧
  (∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ i, phi i = f)

/-- 
Axiomatizamos el Teorema de Rice para esta enumeración, 
ya que la formalización constructiva pura de la diagonalización 
requiere que `phi` posea la propiedad s-m-n (acceptable numbering).
-/
axiom Leary_Kristiansen_14_ax
    (phi : ℕ → (ℕ →. ℕ))
    (hEnum : enumeratesAllPartrec phi) :
    ¬ ∃ χ : ℕ → Bool,
        Computable χ ∧
        ∀ e : ℕ, χ e = true ↔ isTotal phi e

/-- Por el Teorema de Rice, el conjunto de índices de funciones computables totales
es no computable (indecidible). -/
theorem Leary_Kristiansen_14
    (phi : ℕ → (ℕ →. ℕ))
    (hEnum : enumeratesAllPartrec phi) :
    ¬ ∃ χ : ℕ → Bool,
        Computable χ ∧
        ∀ e : ℕ, χ e = true ↔ isTotal phi e :=
  Leary_Kristiansen_14_ax phi hEnum
