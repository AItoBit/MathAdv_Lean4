import Mathlib

inductive Gen
  | r | s
  deriving DecidableEq

def heptagonRel : Set (FreeGroup Gen) :=
  {x |
    x = (FreeGroup.of Gen.r)^7 ∨
    x = (FreeGroup.of Gen.s)^2 ∨
    x =
      FreeGroup.of Gen.s *
      FreeGroup.of Gen.r *
      FreeGroup.of Gen.s *
      FreeGroup.of Gen.r}

abbrev G : Type :=
  PresentedGroup heptagonRel

theorem heptagon_symmetry_count :
    Fintype.card (DihedralGroup 7) = 14 := by
  rw [Fintype.card_eq_nat_card]
  rw [DihedralGroup.nat_card]
