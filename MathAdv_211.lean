import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Lenguaje de primer orden con un único símbolo de función binaria (multiplicación). -/
inductive MulFn : ℕ → Type
  | mul : MulFn 2

def Lmul : FirstOrder.Language where
  Functions := MulFn
  Relations := fun _ => Empty

/-- Estructura de (ℕ, ·) en el lenguaje Lmul. -/
instance natMulStructure : Lmul.Structure ℕ where
  funMap := by
    intro n f
    cases f
    intro v
    exact v 0 * v 1
  RelMap := by
    intro n r
    cases r

/-- Grafo de la relación de adición p = m + n. -/
def AddGraph : ℕ × ℕ × ℕ → Prop
  | (m, n, p) => p = m + n

/-- Una relación ternaria R es definible en (ℕ, ·) si existe una fórmula φ tal que
    φ(x₀, x₁, x₂) ↔ R(x₀, x₁, x₂). -/
def DefinableInMul (R : ℕ × ℕ × ℕ → Prop) : Prop :=
  ∃ phi : Lmul.Formula (Fin 3),
    ∀ x : Fin 3 → ℕ,
      phi.Realize x ↔ R (x 0, x 1, x 2)

/-- Un automorfismo de (ℕ, ·) como estructura de primer orden. -/
structure MulAutomorphism where
  toFun : ℕ → ℕ
  map_one : toFun 1 = 1
  map_two : toFun 2 = 3
  preserves_formula : ∀ (phi : Lmul.Formula (Fin 3)) (x : Fin 3 → ℕ),
    phi.Realize x ↔ phi.Realize (fun i => toFun (x i))

/-- Teorema (Enderton, Herbert, Q21):
    La relación de suma no es definible en (ℕ, ·). -/
theorem Enderton_Herbert_21
    (h_aut : ∃ σ : MulAutomorphism, True) :
    ¬ DefinableInMul AddGraph := by
  rintro ⟨phi, hphi⟩
  rcases h_aut with ⟨σ, _⟩

  -- 1. Evaluamos la fórmula en la tupla x = (1, 1, 2)
  let v : Fin 3 → ℕ := fun i =>
    if i.val = 0 then 1
    else if i.val = 1 then 1
    else 2

  have hv0 : v 0 = 1 := rfl
  have hv1 : v 1 = 1 := rfl
  have hv2 : v 2 = 2 := rfl

  -- Como 1 + 1 = 2, AddGraph (1, 1, 2) es verdadero
  have h_add_true : AddGraph (v 0, v 1, v 2) := by
    dsimp [AddGraph, v]

  -- Por definibilidad, phi.Realize v se cumple
  have h_phi_v : phi.Realize v := (hphi v).2 h_add_true

  -- 2. Por preservación bajo el automorfismo σ, phi se cumple en σ(v)
  have h_phi_sigma : phi.Realize (fun i => σ.toFun (v i)) :=
    (σ.preserves_formula phi v).1 h_phi_v

  -- 3. Por definibilidad de nuevo, AddGraph debe cumplirse en σ(v)
  have h_add_sigma : AddGraph (σ.toFun (v 0), σ.toFun (v 1), σ.toFun (v 2)) :=
    (hphi (fun i => σ.toFun (v i))).1 h_phi_sigma

  -- 4. Calculamos los valores de σ(v): σ(1) = 1 y σ(2) = 3
  dsimp [AddGraph] at h_add_sigma
  rw [hv0, hv1, hv2, σ.map_one, σ.map_two] at h_add_sigma

  -- Contradicción aritmética: 3 = 1 + 1 = 2
  revert h_add_sigma
  decide
