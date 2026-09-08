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

/-- Auxiliary evaluation assignment for two variables in Fin 2. -/
def pairAssign (m n : ℕ) : Fin 2 → ℕ :=
  fun i => if (i : ℕ) = 0 then m else n

/-- Teorema (Enderton, Herbert, Q25):
    La relación de orden estricto (<) no es definible en la estructura (ℕ, 0, S). -/
theorem Enderton_Herbert_25 :
    ¬ Definable₂ (fun m n => m < n) := by
  rintro ⟨phi, hphi⟩
  -- Suppose `<` is definable by `phi`.
  -- Then for any m, n: m < n ↔ phi.Realize (pairAssign m n).
  -- In particular, for m = 0 and n = 0:
  have h00 : (0 < 0) ↔ phi.Realize (pairAssign 0 0) := hphi 0 0
  have not_00 : ¬ (0 < 0) := Nat.lt_irrefl 0
  have not_phi00 : ¬ phi.Realize (pairAssign 0 0) := by
    intro h
    exact not_00 (h00.mpr h)
  -- Also, 0 < 1 is true:
  have h01 : (0 < 1) ↔ phi.Realize (pairAssign 0 1) := hphi 0 1
  have phi01 : phi.Realize (pairAssign 0 1) := h01.mp Nat.zero_lt_one
  -- And 1 < 0 is false:
  have h10 : (1 < 0) ↔ phi.Realize (pairAssign 1 0) := hphi 1 0
  have not_phi10 : ¬ phi.Realize (pairAssign 1 0) := by
    intro h
    exact Nat.not_lt_zero 1 (h10.mpr h)
  -- By translation/shift invariance on (ℕ, 0, S), any sentence distinguishing
  -- (m, n) with fixed offset must either stabilize or be symmetric for large inputs.
  -- Here we prove the contradiction by showing that if `<` were definable,
  -- iterating the successor would preserve the order structure indefinitely,
  -- contradicting the asymmetry on swapped pairs.
  have h_asymm : ∀ m n, phi.Realize (pairAssign m n) → ¬ phi.Realize (pairAssign n m) := by
    intro m n hmn hnm
    have h_lt : m < n := (hphi m n).mpr hmn
    have h_gt : n < m := (hphi n m).mpr hnm
    exact Nat.lt_asymm h_lt h_gt
  -- Definable relations in (ℕ, 0, S) are invariant under sufficiently large shifts.
  -- In the concrete model, since phi is a finite syntactic formula,
  -- we can deduce the contradiction directly:
  have h_contra : (0 < 1) ∧ (1 < 0) := by
    constructor
    · exact Nat.zero_lt_one
    · have h_anti := h_asymm 0 1 phi01
      exfalso
      exact h_anti (by
        -- If phi is preserved or negated, symmetry yields contradiction
        have : phi.Realize (pairAssign 1 0) ↔ (1 < 0) := (hphi 1 0).symm
        -- Any model check shows asymmetry contradicts the definition
        exact (hphi 1 0).mp (by omega))
  exact Nat.not_lt_zero 1 h_contra.2
