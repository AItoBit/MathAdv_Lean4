import Mathlib

/-! # No universal total computable function

Assuming `phi` enumerates all partial recursive unary functions, there is no
function `U : ℕ → ℕ → ℕ` which is (total and) computable and satisfies
`phi k x = U k x` for all `k, x`. -/

abbrev PartFun := ℕ →. ℕ

/-- `phi` enumerates exactly the partial recursive unary functions. -/
def enumeratesAllPartrec (phi : ℕ → PartFun) : Prop :=
  (∀ i, Nat.Partrec (phi i)) ∧ (∀ f : PartFun, Nat.Partrec f → ∃ i, phi i = f)

/-- There is no universal function that is both total and computable:
the nowhere-defined function is partial recursive, hence appears in the
enumeration, but a total universal function would force it to be total. -/
theorem open_logic_5
    (phi : ℕ → PartFun)
    (hEnum : enumeratesAllPartrec phi) :
    ¬ ∃ U : ℕ → ℕ → ℕ,
        (Computable (fun p : ℕ × ℕ => U p.1 p.2)) ∧
        (∀ k x, phi k x = Part.some (U k x)) := by
  rintro ⟨U, -, hU⟩
  obtain ⟨i, hi⟩ := hEnum.2 (fun _ => Part.none) Nat.Partrec.none
  have h := hU i 0
  rw [hi] at h
  exact (Part.eq_none_iff'.mp rfl) (h ▸ Part.some_dom (U i 0))
