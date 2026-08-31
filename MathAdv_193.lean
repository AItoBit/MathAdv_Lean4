import Mathlib

/-- A set `X` is `s`-closed (relative to base point `o`) if it contains `o`
and is closed under `s`. -/
def sClosed {N : Type} (s : N → N) (o : N) (X : Set N) : Prop :=
  o ∈ X ∧ ∀ x ∈ X, s x ∈ X

/-- The `s`-closure of `o`: the intersection of all `s`-closed sets. -/
def sClosure {N : Type} (s : N → N) (o : N) : Set N :=
  ⋂₀ {X : Set N | sClosed s o X}

/-- A Dedekind algebra: `o` is not in the range of `s`, `s` is injective,
and the carrier is the `s`-closure of `o`. -/
structure DedekindAlgebra (N : Type) where
  s : N → N
  o : N
  o_not_in_range : o ∉ Set.range s
  s_inj : Function.Injective s
  carrier_is_closure : ∀ x : N, x ∈ sClosure s o

variable {N : Type} (A : DedekindAlgebra N)

/-- Induction principle for Dedekind algebras: any property holding at `o` and
preserved by `s` holds everywhere. -/
theorem open_logic_3 (phi : N → Prop)
    (h0 : phi A.o)
    (hstep : ∀ n, phi n → phi (A.s n)) :
    ∀ n, phi n := by
  intro n
  have hclosed : sClosed A.s A.o {x | phi x} := ⟨h0, fun x hx => hstep x hx⟩
  exact A.carrier_is_closure n {x | phi x} hclosed
