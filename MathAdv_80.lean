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
# Every polynomial of degree `n` has exactly `n` zeros, counting multiplicity

Multiple-choice question: which theorem or method can be used to answer the question?
The intended answer is **(c) Rouché's theorem**.

The Lean statements below use `Polynomial.roots`, the multiset of roots of a polynomial
over `ℂ`, in which each root occurs with its multiplicity. Its cardinality is therefore
the number of zeros counted with multiplicity.
-/

/-- **Fundamental theorem of algebra (counting multiplicity).**
A polynomial over `ℂ` of degree `n` has exactly `n` complex zeros, counted with
multiplicity. -/
theorem question_6
    (p : Polynomial ℂ) (n : ℕ)
    (hp : p.natDegree = n) :
    Multiset.card p.roots = n := by
  rcases eq_or_ne p 0 with rfl | h
  · simpa using hp
  · rw [← hp]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)

/-- Restatement of `question_6` in terms of root multiplicities: the sum of the
multiplicities of the distinct complex zeros of a polynomial equals its degree. -/
theorem question_6_sum_rootMultiplicity
    (p : Polynomial ℂ) (n : ℕ) (hp : p.natDegree = n) :
    ∑ z ∈ p.roots.toFinset, p.rootMultiplicity z = n := by
  have h : ∑ z ∈ p.roots.toFinset, Multiset.count z p.roots = n := by
    rw [Multiset.toFinset_sum_count_eq]
    exact question_6 p n hp
  rw [← h]
  exact Finset.sum_congr rfl fun z _ => (Polynomial.count_roots p (a := z)).symm

#print axioms question_6
#print axioms question_6_sum_rootMultiplicity
