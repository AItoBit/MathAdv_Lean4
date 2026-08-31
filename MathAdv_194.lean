import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- The universe `|𝔐| = {1, 2, 3}` of the structure. -/
inductive M
  | one | two | three
  deriving DecidableEq, Repr

/-- Interpretation of the constant symbol `c`: `c^𝔐 = 3`. -/
def cM : M := .three

/-- Interpretation of the unary function symbol `f`. -/
def fM : M → M
  | .one   => .two
  | .two   => .three
  | .three => .three

/-- Interpretation of the binary relation symbol `A`:
`A^𝔐 = {(1,2), (2,3), (3,3)}`. -/
def AM : M → M → Prop
  | .one,   .two   => True
  | .two,   .three => True
  | .three, .three => True
  | _,      _      => False

/-- The assignment `s(v) = 1` for every variable `v`. -/
def s : ℕ → M := fun _ => M.one

/-- The variable `z`. -/
def zVar : ℕ := 0

/-- `𝔐, s ⊨ ∃x (A(f(z), c) → ∀y (A(y, x) ∨ A(f(y), x)))`.
Unfolding the inductive definition of satisfaction, this amounts to exhibiting an
`x`-variant of `s` (namely `x := 3`) for which the conditional holds; here the
antecedent `A(f(z), c)` is in fact true, since `f^𝔐(s(z)) = f^𝔐(1) = 2` and
`(2, 3) ∈ A^𝔐`, so one checks all `y`-variants. -/
theorem open_logic_4 :
    ∃ x : M, (AM (fM (s zVar)) cM → ∀ y : M, AM y x ∨ AM (fM y) x) := by
  refine ⟨M.three, fun _ y => ?_⟩
  cases y with
  | one => exact Or.inr trivial
  | two => exact Or.inl trivial
  | three => exact Or.inl trivial
