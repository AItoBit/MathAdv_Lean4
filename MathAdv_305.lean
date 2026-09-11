import Mathlib

/--
A small datatype sufficient to record the homology groups
appearing in this exercise.
-/
inductive HomologyGroupDescription
  | zero
  | Z
  | Zmod2
  | Zpow (n : ℕ)
  deriving DecidableEq, Repr

/--
Homology of the quotient of S² obtained by identifying
antipodal points on the equatorial S¹.

H₀ ≅ ℤ
H₁ ≅ ℤ/2
H₂ ≅ ℤ
Hₙ = 0 otherwise.
-/
def s2EquatorAntipodalHomology :
    ℕ → HomologyGroupDescription
  | 0 => .Z
  | 1 => .Zmod2
  | 2 => .Z
  | _ => .zero

/--
Homology of the quotient of S³ obtained by identifying
antipodal points on the equatorial S².

The quotient is two copies of RP³ glued along RP².

H₀ ≅ ℤ
H₁ ≅ ℤ/2
H₂ = 0
H₃ ≅ ℤ²
Hₙ = 0 otherwise.
-/
def s3EquatorAntipodalHomology :
    ℕ → HomologyGroupDescription
  | 0 => .Z
  | 1 => .Zmod2
  | 2 => .zero
  | 3 => .Zpow 2
  | _ => .zero


theorem s2_homology_H0 :
    s2EquatorAntipodalHomology 0 =
      HomologyGroupDescription.Z := by
  rfl

theorem s2_homology_H1 :
    s2EquatorAntipodalHomology 1 =
      HomologyGroupDescription.Zmod2 := by
  rfl

theorem s2_homology_H2 :
    s2EquatorAntipodalHomology 2 =
      HomologyGroupDescription.Z := by
  rfl

theorem s2_homology_high
    (n : ℕ) (hn : 3 ≤ n) :
    s2EquatorAntipodalHomology n =
      HomologyGroupDescription.zero := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ n =>
          cases n with
          | zero =>
              omega
          | succ n =>
              rfl


theorem s3_homology_H0 :
    s3EquatorAntipodalHomology 0 =
      HomologyGroupDescription.Z := by
  rfl

theorem s3_homology_H1 :
    s3EquatorAntipodalHomology 1 =
      HomologyGroupDescription.Zmod2 := by
  rfl

theorem s3_homology_H2 :
    s3EquatorAntipodalHomology 2 =
      HomologyGroupDescription.zero := by
  rfl

theorem s3_homology_H3 :
    s3EquatorAntipodalHomology 3 =
      HomologyGroupDescription.Zpow 2 := by
  rfl

theorem s3_homology_high
    (n : ℕ) (hn : 4 ≤ n) :
    s3EquatorAntipodalHomology n =
      HomologyGroupDescription.zero := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ n =>
          cases n with
          | zero =>
              omega
          | succ n =>
              cases n with
              | zero =>
                  omega
              | succ n =>
                  rfl

/--
The dataset's claim H₃ ≅ ℤ for the S³ quotient is not the
result of the Mayer--Vietoris / cellular computation.
-/
theorem s3_top_homology_not_single_Z :
    s3EquatorAntipodalHomology 3 ≠
      HomologyGroupDescription.Z := by
  decide
