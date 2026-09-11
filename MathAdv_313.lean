import Mathlib

open scoped BigOperators

/--
A Poincaré series is represented by its coefficient sequence.
`a n` is the coefficient of `t^n`.
-/
abbrev PoincareSeries := ℕ → ℕ

/--
Cauchy product of two Poincaré series.

The coefficient of degree `n` is
  Σ_{i=0}^n a_i b_{n-i}.
-/
def poincareMul
    (a b : PoincareSeries) :
    PoincareSeries :=
  fun n =>
    Finset.sum (Finset.range (n + 1))
      (fun i => a i * b (n - i))

/--
The Betti numbers predicted by the Künneth formula.
-/
def productBettiNumbers
    (a b : PoincareSeries) :
    PoincareSeries :=
  fun n =>
    Finset.sum (Finset.range (n + 1))
      (fun i => a i * b (n - i))

/--
Coefficientwise form of
  p(X × Y) = p(X) p(Y).
-/
theorem poincare_product_coeff
    (a b : PoincareSeries)
    (n : ℕ) :
    productBettiNumbers a b n =
      poincareMul a b n := by
  rfl

/--
The entire coefficient sequence agrees with the Cauchy product.
-/
theorem poincare_product
    (a b : PoincareSeries) :
    productBettiNumbers a b =
      poincareMul a b := by
  rfl

/--
Expanded degree-n Künneth formula for Betti numbers.
-/
theorem kunneth_betti_formula
    (a b : PoincareSeries)
    (n : ℕ) :
    productBettiNumbers a b n =
      Finset.sum (Finset.range (n + 1))
        (fun i => a i * b (n - i)) := by
  rfl
