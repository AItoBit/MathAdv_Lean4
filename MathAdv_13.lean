import Mathlib

/-!
# A finite integral domain is a field

**Problem.** Show that a finite integral domain is a field.

**Which fact can be used?** (d) *Injective implies surjective on a finite set.*

Indeed, for `a ≠ 0` in an integral domain `R`, the map `x ↦ a * x` is injective
(cancellation, since `R` has no zero divisors). As `R` is finite, this map is
therefore surjective, so `1` is in its image: there is `b` with `a * b = 1`.
Hence every nonzero element is a unit, i.e. `R` is a field.
-/

/-- The key step: on a finite integral domain, multiplication by a nonzero
element is a bijection (injective, hence surjective since the set is finite). -/
theorem mul_left_bijective_of_finite_domain
    (R : Type*) [CommRing R] [IsDomain R] [Finite R] {a : R} (ha : a ≠ 0) :
    Function.Bijective (fun x : R => a * x) := by
  have hinj : Function.Injective (fun x : R => a * x) := fun x y h =>
    mul_left_cancel₀ ha h
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- Every nonzero element of a finite integral domain is invertible. -/
theorem Gallian_14
    (R : Type*) [CommRing R] [IsDomain R] [Fintype R] :
    ∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1 ∧ b * a = 1 := by
  intro a ha
  obtain ⟨b, hb⟩ := (mul_left_bijective_of_finite_domain R ha).2 1
  exact ⟨b, hb, by rw [mul_comm]; exact hb⟩

/-- A finite integral domain is a field. -/
theorem isField_of_finite_domain
    (R : Type*) [CommRing R] [IsDomain R] [Fintype R] : IsField R where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := fun {a} ha => by
    obtain ⟨b, hb, _⟩ := Gallian_14 R a ha
    exact ⟨b, hb⟩
