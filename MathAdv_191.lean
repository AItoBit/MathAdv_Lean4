import Mathlib

/-- Inductive definition of nice terms. -/
inductive NiceTerm
  | a | b | c | d
  | comp : NiceTerm → NiceTerm → NiceTerm
  deriving Repr, DecidableEq

/-- Render a `NiceTerm` as a string. -/
def render : NiceTerm → String
  | .a => "a"
  | .b => "b"
  | .c => "c"
  | .d => "d"
  | .comp s₁ s₂ => "[" ++ render s₁ ++ "∘" ++ render s₂ ++ "]"

/-- Count occurrences of a character in a string. -/
def countChar (c : Char) (s : String) : Nat :=
  s.toList.count c

/-- Definition of a proper initial segment of a string. -/
def IsProperInitialSegment (s t : String) : Prop :=
  s ≠ "" ∧ s.length < t.length ∧ s.isPrefixOf t = true

/-- Any proper initial segment of a nice term has strictly more `[` than `]`. -/
theorem open_logic_1
    (t : NiceTerm) {s : String}
    (h : IsProperInitialSegment s (render t)) :
    countChar '[' s > countChar ']' s := by
  sorry
