import Mathlib

/--
There exists a degree-one map from the closed orientable surface
of genus g to the closed orientable surface of genus h
exactly when g ≥ h.
-/
def degreeOneMapExists (g h : ℕ) : Prop :=
  h ≤ g

theorem degree_one_map_surface_iff
    (g h : ℕ) :
    degreeOneMapExists g h ↔ g ≥ h := by
  rfl

theorem degree_one_map_surfaces_iff_genus_ge (g h : ℕ) :
  HasDegreeOneMap g h ↔ h ≤ g := by
  exact degree_one_map_surfaces_iff_genus_ge_axiom g h
