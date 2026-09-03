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

/-- A model of the axiom system `N` for the language
`L_NT = {0, S, +, ⬝, E, <}`. -/
structure NTStructure where
  M   : Type
  zero : M
  succ : M → M
  add  : M → M → M
  mul  : M → M → M
  exp  : M → M → M
  lt   : M → M → Prop
  ax1 : ∀ x : M, succ x ≠ zero
  ax2 : ∀ ⦃x y : M⦄, succ x = succ y → x = y
  ax3 : ∀ x : M, add x zero = x
  ax4 : ∀ x y : M, add x (succ y) = succ (add x y)
  ax5 : ∀ x : M, mul x zero = zero
  ax6 : ∀ x y : M, mul x (succ y) = add (mul x y) x
  ax7 : ∀ x : M, exp x zero = succ zero
  ax8 : ∀ x y : M, exp x (succ y) = mul (exp x y) x
  ax9 : ∀ x : M, ¬ lt x zero
  ax10 : ∀ x y : M, lt x (succ y) ↔ (lt x y ∨ x = y)
  ax11 : ∀ x y : M, lt x y ∨ x = y ∨ lt y x

namespace LearyModel

/-- The universe of the model: the natural numbers together with one extra
element `none` ("infinity"), which is its own successor. -/
abbrev M := Option ℕ

/-- Successor: the usual one on `ℕ`, with `none` a fixed point. -/
def succ : M → M
  | none => none
  | some n => some (n + 1)

/-- Addition: the usual one on `ℕ`; anything involving `none` is `none`. -/
def add : M → M → M
  | some m, some n => some (m + n)
  | _, _ => none

/-- Multiplication. -/
def mul : M → M → M
  | some m, some n => some (m * n)
  | none, some 0 => some 0
  | none, some (_ + 1) => none
  | _, none => none

/-- Exponentiation. -/
def exp : M → M → M
  | some m, some n => some (m ^ n)
  | none, some 0 => some 1
  | none, some (_ + 1) => none
  | some 0, none => some 0
  | some (_ + 1), none => none
  | none, none => none

/-- Order: the usual one on `ℕ`, with `none` strictly above everything,
including itself. -/
def lt : M → M → Prop
  | _, none => True
  | none, some _ => False
  | some m, some n => m < n

lemma add_none (x : M) : add x none = none := by cases x <;> rfl

lemma mul_none (x : M) : mul x none = none := by cases x <;> rfl

/-- The model, packaged as an `NTStructure`. -/
def model : NTStructure where
  M := M
  zero := some 0
  succ := succ
  add := add
  mul := mul
  exp := exp
  lt := lt
  ax1 := by rintro (_ | n) <;> simp [succ]
  ax2 := by rintro (_ | m) (_ | n) h <;> simp_all [succ]
  ax3 := by rintro (_ | m) <;> rfl
  ax4 := by rintro (_ | m) (_ | n) <;> simp [succ, add]; omega
  ax5 := by rintro (_ | m) <;> rfl
  ax6 := by
    rintro (_ | m) (_ | n)
    · simp [succ, mul, add]
    · simp [succ, add_none]; rfl
    · simp [succ, mul]; rfl
    · simp [succ, mul, add, Nat.mul_succ]
  ax7 := by rintro (_ | m) <;> rfl
  ax8 := by
    rintro (_ | m) (_ | n)
    · rfl
    · simp [succ, exp, mul_none]
    · cases m <;> simp [succ, exp, mul]
    · simp [succ, exp, mul, pow_succ]
  ax9 := by rintro (_ | m) <;> simp [lt]
  ax10 := by
    rintro (_ | m) (_ | n) <;> simp [succ, lt]; omega
  ax11 := by
    rintro (_ | m) (_ | n) <;> simp [lt]; omega

end LearyModel

/-- `N ⊬ (∀x) ¬(x < x)`: there is a model of `N` containing an element
`a` with `a < a`. -/
theorem Leary_Kristiansen_11 :
    ∃ A : NTStructure, ∃ a : A.M, A.lt a a :=
  ⟨LearyModel.model, none, trivial⟩

/-- Equivalent phrasing: the sentence `(∀x) ¬(x < x)` is not a semantic
consequence of `N`, hence (by soundness) not provable from `N`. -/
theorem Leary_Kristiansen_11' :
    ¬ (∀ A : NTStructure, ∀ a : A.M, ¬ A.lt a a) := by
  obtain ⟨A, a, ha⟩ := Leary_Kristiansen_11
  exact fun h => h A a ha

/-- Demostración por construcción: existe un modelo de N donde algún elemento satisface `lt a a`. -/
theorem Leary_Kristiansen_11 :
  ∃ A : NTStructure, ∃ a : A.M, A.lt a a := by
  sorry
