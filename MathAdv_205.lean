import Mathlib

inductive BTFunc : ℕ → Type
  | zero : BTFunc 0
  | one  : BTFunc 0
  | e    : BTFunc 0
  | circ : BTFunc 2

def BTRel : ℕ → Type := fun _ => Empty

def LBT : FirstOrder.Language where
  Functions := BTFunc
  Relations := BTRel

private def app0BT {M : Type} (I : LBT.Structure M)
    (f0 : LBT.Functions 0) : M :=
  let v0 : Fin 0 → M := fun i => nomatch i
  I.funMap f0 v0

def zeroBT {M : Type} (I : LBT.Structure M) : M :=
  app0BT I BTFunc.zero

def oneBT {M : Type} (I : LBT.Structure M) : M :=
  app0BT I BTFunc.one

def eBT {M : Type} (I : LBT.Structure M) : M :=
  app0BT I BTFunc.e

def circBT {M : Type} (I : LBT.Structure M) (x y : M) : M :=
  I.funMap
    BTFunc.circ
    (fun i : Fin 2 => Fin.cases x (fun _ => y) i)

/-- Contramodelo: List (Fin 3) donde 0 = [0], 1 = [1], e = [], circ = (++) y el elemento x = [2]. -/
theorem Leary_Kristiansen_15 :
  ∃ (M : Type) (I : LBT.Structure M),
    (∀ x : M, x = circBT I (eBT I) x) ∧
    (∀ x : M, x = circBT I x (eBT I)) ∧
    (∀ x y z : M, circBT I (circBT I x y) z = circBT I x (circBT I y z)) ∧
    (∀ x : M, circBT I (zeroBT I) x ≠ eBT I ∧ circBT I (oneBT I) x ≠ eBT I) ∧
    (∀ x y : M, x ≠ y →
        circBT I (zeroBT I) x ≠ circBT I (zeroBT I) y ∧
        circBT I (oneBT I) x ≠ circBT I (oneBT I) y) ∧
    (∀ x y : M, circBT I (zeroBT I) x ≠ circBT I (oneBT I) y) ∧
    ∃ x : M,
      x ≠ eBT I ∧
      (∀ y : M, circBT I (zeroBT I) y ≠ x ∧ circBT I (oneBT I) y ≠ x) := by
  -- Definimos el tipo M como listas sobre Fin 3
  let M := List (Fin 3)
  
  -- Definimos la estructura sobre M
  let I : LBT.Structure M := {
    funMap := by
      intro n f
      cases f with
      | zero => intro _; exact [(0 : Fin 3)]
      | one  => intro _; exact [(1 : Fin 3)]
      | e    => intro _; exact ([] : List (Fin 3))
      | circ => intro v; exact v 0 ++ v 1
    RelMap := by
      intro n r
      cases r
  }

  use M, I

  have h_e : eBT I = ([] : List (Fin 3)) := rfl
  have h_zero : zeroBT I = [(0 : Fin 3)] := rfl
  have h_one : oneBT I = [(1 : Fin 3)] := rfl
  have h_circ : ∀ x y : M, circBT I x y = x ++ y := by
    intro x y
    rfl

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. x = e ++ x
    intro x
    rw [h_e, h_circ]
    exact (List.nil_append x).symm
  · -- 2. x = x ++ e
    intro x
    rw [h_e, h_circ]
    exact (List.append_nil x).symm
  · -- 3. (x ++ y) ++ z = x ++ (y ++ z)
    intro x y z
    rw [h_circ, h_circ, h_circ, h_circ]
    exact List.append_assoc x y z
  · -- 4. 0 ++ x ≠ e ∧ 1 ++ x ≠ e
    intro x
    rw [h_zero, h_one, h_e, h_circ, h_circ]
    constructor
    · intro h
      cases h
    · intro h
      cases h
  · -- 5. x ≠ y → 0 ++ x ≠ 0 ++ y ∧ 1 ++ x ≠ 1 ++ y
    intro x y hne
    rw [h_zero, h_one, h_circ, h_circ, h_circ, h_circ]
    constructor
    · intro h
      injection h with _ htail
      exact hne htail
    · intro h
      injection h with _ htail
      exact hne htail
  · -- 6. 0 ++ x ≠ 1 ++ y
    intro x y
    rw [h_zero, h_one, h_circ, h_circ]
    intro h
    injection h with hhead _
    revert hhead
    decide
  · -- 7. Existe x = [2] tal que x ≠ e y no empieza ni con 0 ni con 1
    use [(2 : Fin 3)]
    constructor
    · rw [h_e]
      intro h
      cases h
    · intro y
      rw [h_zero, h_one, h_circ, h_circ]
      constructor
      · intro h
        injection h with hhead _
        revert hhead
        decide
      · intro h
        injection h with hhead _
        revert hhead
        decide
