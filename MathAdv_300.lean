import Mathlib

abbrev ZGroup := Multiplicative ℤ

abbrev TwoToriGluedFundamentalGroup :=
  (Monoid.Coprod ZGroup ZGroup) × ZGroup

theorem two_tori_glued_group :
    TwoToriGluedFundamentalGroup =
      ((Monoid.Coprod ZGroup ZGroup) × ZGroup) := by
  rfl
