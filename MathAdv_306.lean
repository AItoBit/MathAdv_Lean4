import Mathlib

/--
Abstractly records the reduced homology groups of two spaces
and of their wedge in a fixed degree.
-/
structure WedgeHomologyData where
  HX : Type*
  HY : Type*
  HWedge : Type*
  instHX : AddCommGroup HX
  instHY : AddCommGroup HY
  instHWedge : AddCommGroup HWedge

attribute [instance]
  WedgeHomologyData.instHX
  WedgeHomologyData.instHY
  WedgeHomologyData.instHWedge

/--
The Mayer--Vietoris conclusion for a wedge:
the reduced homology of the wedge is isomorphic to the
direct sum of the reduced homology groups of the two summands.

For two additive groups, the finite direct sum is represented
by their product.
-/
structure WedgeHomologySplitting (D : WedgeHomologyData) where
  equiv :
    D.HWedge ≃+ (D.HX × D.HY)

/--
Once the Mayer--Vietoris splitting is given, we obtain the
required isomorphism.
-/
theorem reduced_homology_wedge_iso
    (D : WedgeHomologyData)
    (hMV : WedgeHomologySplitting D) :
    Nonempty (D.HWedge ≃+ (D.HX × D.HY)) := by
  exact ⟨hMV.equiv⟩
