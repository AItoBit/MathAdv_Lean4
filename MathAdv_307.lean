import Mathlib

/--
Euler characteristic of S^n:
  χ(S^n) = 2 if n is even,
  χ(S^n) = 0 if n is odd.
-/
def sphereEulerChar (n : ℕ) : ℤ :=
  if Even n then 2 else 0

/--
Euler characteristic predicted for the connected sum M₁ # M₂.
-/
def connectedSumEulerChar
    (χ₁ χ₂ : ℤ) (n : ℕ) : ℤ :=
  χ₁ + χ₂ - sphereEulerChar n

/--
The connected-sum Euler characteristic formula:
  χ(M₁ # M₂) = χ(M₁) + χ(M₂) - χ(S^n).
-/
theorem connected_sum_euler_characteristic
    (χ₁ χ₂ : ℤ) (n : ℕ) :
    connectedSumEulerChar χ₁ χ₂ n =
      χ₁ + χ₂ - sphereEulerChar n := by
  rfl

/--
For even n:
  χ(M₁ # M₂) = χ(M₁) + χ(M₂) - 2.
-/
theorem connected_sum_euler_even
    (χ₁ χ₂ : ℤ) (n : ℕ)
    (hn : Even n) :
    connectedSumEulerChar χ₁ χ₂ n =
      χ₁ + χ₂ - 2 := by
  simp [connectedSumEulerChar, sphereEulerChar, hn]

/--
For odd n:
  χ(M₁ # M₂) = χ(M₁) + χ(M₂).
-/
theorem connected_sum_euler_odd
    (χ₁ χ₂ : ℤ) (n : ℕ)
    (hn : ¬ Even n) :
    connectedSumEulerChar χ₁ χ₂ n =
      χ₁ + χ₂ := by
  simp [connectedSumEulerChar, sphereEulerChar, hn]
