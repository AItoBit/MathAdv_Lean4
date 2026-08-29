import Mathlib

/-!
# Surjective images of local rings are local

If `R` is a local ring and `f : R →+* S` is a surjective ring homomorphism onto a nonzero
ring `S`, then `S` is local.

(In current Mathlib the typeclass formerly named `LocalRing` is called `IsLocalRing`.)
-/

/-- The image of a unit under a ring homomorphism is a unit. -/
theorem isUnit_map_of_isUnit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r : R}
    (hr : IsUnit r) : IsUnit (f r) :=
  hr.map f

/-- Key step: in a surjective image of a local ring, for every element `s` either `s` or
`1 - s` is a unit. -/
theorem isUnit_or_isUnit_one_sub_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) (hf : Function.Surjective f) (s : S) :
    IsUnit s ∨ IsUnit (1 - s) := by
  obtain ⟨r, rfl⟩ := hf s
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with h | h
  · exact Or.inl (h.map f)
  · exact Or.inr (by simpa using h.map f)

/-- **Main theorem.** A surjective ring-homomorphic image of a local ring, if nonzero,
is again a local ring. -/
theorem Q26
    {R S : Type*}
    [CommRing R] [CommRing S]
    [IsLocalRing R]
    [Nontrivial S]
    (f : R →+* S)
    (hf : Function.Surjective f) :
    IsLocalRing S :=
  .of_isUnit_or_isUnit_one_sub_self (isUnit_or_isUnit_one_sub_of_surjective f hf)
