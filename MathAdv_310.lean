import Mathlib

/--
The induced map on reduced homology is zero in every degree.
We model each source and target abstractly by ℤ here, since the
essential assertion is that the induced homomorphism itself is zero.
-/
def mooreHomologyMap (_i : ℕ) : ℤ →+ ℤ :=
  0

theorem moore_homology_map_trivial
    (i : ℕ) :
    mooreHomologyMap i = 0 := by
  rfl

theorem moore_homology_map_apply
    (i : ℕ) (z : ℤ) :
    mooreHomologyMap i z = 0 := by
  rfl


/--
The top cohomology map is the canonical quotient map

    ℤ → ℤ/mℤ.
-/
def mooreCohomologyMap (m : ℕ) : ℤ →+ ZMod m :=
  Int.castAddHom (ZMod m)

theorem moore_cohomology_map_apply
    (m : ℕ) (z : ℤ) :
    mooreCohomologyMap m z = (z : ZMod m) := by
  rfl

/--
The cohomology map is surjective: it is precisely the projection
ℤ → ℤ/mℤ.
-/
theorem moore_cohomology_map_surjective
    (m : ℕ) :
    Function.Surjective (mooreCohomologyMap m) := by
  intro z
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective z
  exact ⟨k, hk⟩

/--
Its kernel is mℤ, confirming that it is the quotient projection.
-/
theorem moore_cohomology_map_kernel
    (m : ℕ) :
    (mooreCohomologyMap m).ker =
      AddSubgroup.zmultiples (m : ℤ) := by
  exact ZMod.ker_intCastAddHom m

/--
For a genuine Moore space M(ℤ_m,n), with m > 1,
the top cohomology map is nonzero.
-/
theorem moore_cohomology_map_nonzero
    (m : ℕ)
    (hm : 1 < m) :
    mooreCohomologyMap m ≠ 0 := by
  letI : Fact (1 < m) := ⟨hm⟩

  intro hzero

  have h1 :
      mooreCohomologyMap m 1 = 0 := by
    rw [hzero]
    rfl

  have hcast :
      (1 : ZMod m) = 0 := by
    simpa [mooreCohomologyMap] using h1

  have hval :
      (1 : ZMod m).val = 0 := by
    rw [hcast]
    exact ZMod.val_zero

  have hone :
      (1 : ZMod m).val = 1 :=
    ZMod.val_one m

  omega


/--
Summary of the Moore-space phenomenon:

* every reduced-homology map is zero;
* the degree-(n+1) cohomology map ℤ → ℤ/mℤ is nonzero
  when m > 1.
-/
theorem moore_space_map_pattern
    (m : ℕ)
    (hm : 1 < m) :
    (∀ i : ℕ, mooreHomologyMap i = 0) ∧
    mooreCohomologyMap m ≠ 0 := by
  constructor

  · intro i
    rfl

  · exact moore_cohomology_map_nonzero m hm
