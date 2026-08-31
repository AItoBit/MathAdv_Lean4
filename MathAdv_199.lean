import Mathlib

/-!
# Trichotomy for von Neumann ordinals

For any two ordinals `α`, `β`, exactly one of `α < β`, `β < α`, `α = β` holds
(here `<` is the membership order on von Neumann ordinals).
-/

/-- Trichotomy of the ordinal order: for any ordinals `α` and `β`,
either `α < β`, or `β < α`, or `α = β`. -/
theorem open_logic_9 (α β : Ordinal) :
    α < β ∨ β < α ∨ α = β := by
  rcases lt_trichotomy α β with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
