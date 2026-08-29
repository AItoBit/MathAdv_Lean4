import Mathlib

/-!
# A commutative ring with identity is local iff `r + s = 1` implies `r` or `s` is a unit

The original statement was phrased with `LocalRing`, which in the current Mathlib is named
`IsLocalRing`.  Being a local ring includes the requirement that the ring is nontrivial, so a
`Nontrivial R` hypothesis is needed: in the zero ring the right-hand condition holds (every
element, being `1`, is a unit) while the ring is not local.  This is recorded in
`zero_ring_not_isLocalRing` below.
-/

/-- A nontrivial commutative ring with identity is local if and only if for all `r s : R`,
`r + s = 1` implies that `r` or `s` is a unit. -/
theorem Q24 (R : Type*) [CommRing R] [Nontrivial R] :
    (IsLocalRing R) ↔ (∀ r s : R, r + s = (1 : R) → IsUnit r ∨ IsUnit s) := by
  constructor
  · intro _ r s hrs
    exact IsLocalRing.isUnit_or_isUnit_of_add_one hrs
  · intro h
    exact { isUnit_or_isUnit_of_add_one := fun {a b} hab => h a b hab }

/-- The nontriviality hypothesis in `Q24` cannot be dropped: in the zero ring the right-hand
condition holds vacuously, yet the zero ring is not a local ring. -/
theorem zero_ring_not_isLocalRing :
    (∀ r s : PUnit, r + s = (1 : PUnit) → IsUnit r ∨ IsUnit s) ∧ ¬ IsLocalRing PUnit := by
  refine ⟨fun r s _ => Or.inl ?_, fun h => (not_nontrivial PUnit) h.toNontrivial⟩
  simp [Subsingleton.elim r (1 : PUnit)]
