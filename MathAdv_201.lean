import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-- Estructura para el lenguaje de Number Theory (L_NT) junto con los axiomas de N. -/
structure NTStructure where
  M    : Type
  zero : M
  succ : M → M
  add  : M → M → M
  mul  : M → M → M
  exp  : M → M → M
  lt   : M → M → Prop
  ax1  : ∀ x : M, succ x ≠ zero
  ax2  : ∀ ⦃x y : M⦄, succ x = succ y → x = y
  ax3  : ∀ x : M, add x zero = x
  ax4  : ∀ x y : M, add x (succ y) = succ (add x y)
  ax5  : ∀ x : M, mul x zero = zero
  ax6  : ∀ x y : M, mul x (succ y) = add (mul x y) x
  ax7  : ∀ x : M, exp x zero = succ zero
  ax8  : ∀ x y : M, exp x (succ y) = mul (exp x y) x
  ax9  : ∀ x : M, ¬ lt x zero
  ax10 : ∀ x y : M, lt x (succ y) ↔ (lt x y ∨ x = y)
  ax11 : ∀ x y : M, lt x y ∨ x = y ∨ lt y x

/-- Demostración por construcción: existe un modelo de N donde algún elemento satisface `lt a a`. -/
theorem Leary_Kristiansen_11 :
  ∃ A : NTStructure, ∃ a : A.M, A.lt a a := by
  sorry
