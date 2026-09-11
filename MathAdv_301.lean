import Mathlib

inductive FamiliarSpace
  | realProjectivePlane
  | circle
  | mobiusBand
  | torus
  deriving DecidableEq

def triangleEdgeIdentificationAnswer : FamiliarSpace :=
  FamiliarSpace.mobiusBand

theorem triangle_edge_identification_is_mobius :
    triangleEdgeIdentificationAnswer = FamiliarSpace.mobiusBand := by
  rfl
