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

/-- **Klement, Exercise 4.9.** Let `f : ω^n → ω` be an `n`-ary function on `ω` and let `χ` be
(the characteristic function of) its graph. If `χ` is recursive, then so is `f`.

The proof is by *closure under minimization*: `f x` is recovered as
`μ y. χ(x, y) = true`, and this search terminates because `f x` itself satisfies the predicate. -/
theorem Klement_7
    {n : Nat}
    (f  : (Fin n → ℕ) → ℕ)
    (χ  : ((Fin n → ℕ) × ℕ) → Bool)
    (hχ : Computable χ)
    (spec : ∀ x y, χ (x, y) = true ↔ y = f x) :
    Computable f := by
  have hp : Partrec₂ (fun (x : Fin n → ℕ) (y : ℕ) => (Part.some (χ (x, y)) : Part Bool)) :=
    (hχ.comp (Computable.pair Computable.fst Computable.snd)).partrec
  refine (Partrec.rfind hp).of_eq ?_
  intro x
  apply Part.eq_some_iff.2
  rw [Nat.mem_rfind]
  constructor
  · simp [(spec x (f x)).2 rfl]
  · intro m hm
    have hne : m ≠ f x := ne_of_lt hm
    have hfalse : χ (x, m) = false := by
      cases h : χ (x, m)
      · rfl
      · exfalso
        exact hne ((spec x m).1 h)
    simp [hfalse]
