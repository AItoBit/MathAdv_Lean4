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

/-!
# The power set of `ℕ` is not enumerable

The original problem asks to show that `𝒫(ℕ)` is not enumerable, i.e. there is no
surjection `ℕ → Set ℕ` (Cantor's diagonal argument).

The multiple-choice question asks which method *cannot* be used to solve the problem;
the answer is (d), the Archimedean property.
-/

/-- The answer to the multiple choice question: the Archimedean property (option (d))
cannot be used to prove that `𝒫(ℕ)` is not enumerable. -/
def open_logic_2_answer : String := "(d)"

/-- `𝒫(ℕ)` is not enumerable: there is no surjection `ℕ → Set ℕ`. -/
theorem open_logic_2a :
    ¬ ∃ f : ℕ → Set ℕ, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact Function.cantor_surjective f hf

/-- `𝒫(ℕ)` is not countable. -/
theorem open_logic_2b :
    ¬ Countable (Set ℕ) := by
  intro h
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective f hf
