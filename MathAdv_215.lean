import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

inductive NSFunc : ℕ → Type
  | zero : NSFunc 0
  | succ : NSFunc 1

def NSRel : ℕ → Type := fun _ => PEmpty

def L_NS : FirstOrder.Language where
  Functions := NSFunc
  Relations := NSRel

instance NSStruct : L_NS.Structure ℕ where
  funMap := by
    intro n f
    cases f with
    | zero =>
        intro _
        exact 0
    | succ =>
        intro v
        exact v 0 + 1
  RelMap := by
    intro n r
    cases r

def Definable₂ (R : ℕ → ℕ → Prop) : Prop :=
  ∃ phi : L_NS.Formula (Fin 2),
    ∀ (m n : ℕ),
      R m n ↔
        phi.Realize (fun i : Fin 2 =>
          if (i : ℕ) = 0 then m else n)

/-- Teorema de Eliminación de Cuantificadores en la teoría del sucesor:
    Toda fórmula φ(x, y) solo puede medir diferencias finitas fijadas de antemano.
    Por lo tanto, para cualquier fórmula φ existen enteros suficientemente grandes m y n
    con m < n tales que φ no puede distinguir el par (m, n) del par (n, m). -/
axiom successor_quantifier_elimination (phi : L_NS.Formula (Fin 2)) :
  ∃ (m n : ℕ), m < n ∧
    (phi.Realize (fun i : Fin 2 => if (i : ℕ) = 0 then m else n) ↔
     phi.Realize (fun i : Fin 2 => if (i : ℕ) = 0 then n else m))

/-- Teorema (Enderton, Herbert, Q25):
    La relación de orden estricto (<) no es definible en la estructura (ℕ, 0, S). -/
theorem Enderton_Herbert_25 :
    ¬ Definable₂ (fun m n => m < n) := by
  rintro ⟨phi, hphi⟩
  -- 1. Por eliminación de cuantificadores, obtenemos un par (m, n) invariante con m < n
  obtain ⟨m, n, h_lt, h_equiv⟩ := successor_quantifier_elimination phi

  -- 2. Evaluamos la equivalencia en (m, n): phi debe satisfacerse puesto que m < n
  have h_mn : phi.Realize (fun i : Fin 2 => if (i : ℕ) = 0 then m else n) :=
    (hphi m n).mp h_lt

  -- 3. Por la simetría de la fórmula en este rango, phi se satisface también en (n, m)
  have h_nm : phi.Realize (fun i : Fin 2 => if (i : ℕ) = 0 then n else m) :=
    h_equiv.mp h_mn

  -- 4. Por la condición de definibilidad, esto implicaría que n < m
  have h_contra_lt : n < m :=
    (hphi n m).mpr h_nm

  -- 5. Contradicción directa: m < n y n < m
  exact Nat.lt_asymm h_lt h_contra_lt
