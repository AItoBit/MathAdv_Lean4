import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

inductive LFn : ℕ → Type
  | add : LFn 2
  | mul : LFn 2
  | z   : LFn 0
  | o   : LFn 0

def LRel : ℕ → Type := fun _ => Empty

def L : FirstOrder.Language where
  Functions := LFn
  Relations := LRel

inductive LcFn : ℕ → Type
  | ofL : ∀ n, L.Functions n → LcFn n
  | c   : LcFn 0

def LcRel : ℕ → Type := fun _ => Empty

def Lc : FirstOrder.Language where
  Functions := LcFn
  Relations := LcRel

instance NatLStructure : L.Structure ℕ where
  funMap := by
    intro n f
    cases f with
    | add =>
        intro v
        exact v 0 + v 1
    | mul =>
        intro v
        exact v 0 * v 1
    | z =>
        intro _
        exact 0
    | o =>
        intro _
        exact 1
  RelMap := by
    intro n r
    cases r

/-- Explicit parameterized structure on ℕ interpreting the constant `c` as `cVal`. -/
def natLcStructure (cVal : ℕ) : Lc.Structure ℕ where
  funMap := by
    intro n f
    cases f with
    | ofL n f' =>
        cases f' with
        | add =>
            intro v
            exact v 0 + v 1
        | mul =>
            intro v
            exact v 0 * v 1
        | z =>
            intro _
            exact 0
        | o =>
            intro _
            exact 1
    | c =>
        intro _
        exact cVal
  RelMap := by
    intro n r
    cases r

def ThNat : L.Theory := L.completeTheory ℕ

private def app0 {Λ : FirstOrder.Language} {M : Type} (S : Λ.Structure M)
    (f0 : Λ.Functions 0) : M :=
  let v0 : Fin 0 → M := fun i => nomatch i
  S.funMap f0 v0

def cValOf {M : Type} (I : Lc.Structure M) : M :=
  app0 (Λ := Lc) I LcFn.c

def zeroOf {M : Type} (I : Lc.Structure M) : M :=
  app0 (Λ := Lc) I (LcFn.ofL 0 LFn.z)

def oneOf {M : Type} (I : Lc.Structure M) : M :=
  app0 (Λ := Lc) I (LcFn.ofL 0 LFn.o)

def addOf {M : Type} (I : Lc.Structure M) (x y : M) : M :=
  I.funMap
    (LcFn.ofL 2 LFn.add)
    (fun i : Fin 2 => Fin.cases x (fun _ => y) i)

def mulOf {M : Type} (I : Lc.Structure M) (x y : M) : M :=
  I.funMap
    (LcFn.ofL 2 LFn.mul)
    (fun i : Fin 2 => Fin.cases x (fun _ => y) i)

def nbarVal {M : Type} (I : Lc.Structure M) : Nat → M
  | 0     => zeroOf I
  | n + 1 => addOf I (nbarVal I n) (oneOf I)

/-- By the Compactness Theorem, the theory Th(ℕ) ∪ {c ≠ n̄ | n ∈ ℕ} has a model. -/
theorem Manin_Zilber_6 :
  ∃ (M : Type) (I : Lc.Structure M) (J : L.Structure M),
    (∀ (n : Nat) (f : L.Functions n) (v : Fin n → M),
       J.funMap f v = I.funMap (LcFn.ofL n f) v) ∧
    (∀ (phi : L.Sentence), ThNat phi →
       @FirstOrder.Language.Sentence.Realize L M J phi) ∧
    (∀ n : Nat, cValOf I ≠ nbarVal I n) := by
  sorry
