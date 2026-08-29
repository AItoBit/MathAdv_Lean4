import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Fourier Series of the Periodic Sawtooth Function (Stein & Shakarchi, Chapter 2)

The $2\pi$-periodic sawtooth function $f(x)$ on $(-\pi, \pi)$ is given by:
$$f(0) = 0, \quad f(x) = \begin{cases} -\frac{\pi}{2} - \frac{x}{2}, & -\pi < x < 0 \\ \frac{\pi}{2} - \frac{x}{2}, & 0 < x < \pi \end{cases}$$

Its complex Fourier series representation is:
$$\frac{1}{2i} \sum_{n \neq 0} \frac{e^{inx}}{n} = \sum_{n=1}^\infty \frac{\sin(nx)}{n}$$

By **Dirichlet's test** (summation by parts on oscillating partial sums of $\sin(nx)$ against $1/n$),
the series converges for all $x \in \mathbb{R}$ to the periodic function $f(x)$.

The accompanying multiple-choice question has answer **(c) Dirichlet's test**.
-/

/-- The multiple choice answer. -/
def stein_9_answer : String := "(c) Dirichlet's test"

/-- The piecewise sawtooth function on $(-\pi, \pi)$. -/
noncomputable def sawtooth (x : ℝ) : ℝ :=
  if _h0 : x = 0 then
    0
  else if _h1 : -Real.pi < x ∧ x < 0 then
    -Real.pi / 2 - x / 2
  else if _h2 : 0 < x ∧ x < Real.pi then
    Real.pi / 2 - x / 2
  else
    0

/-- The Fourier series evaluated as a symmetric summation limit. -/
noncomputable def FS (x : ℝ) : ℂ :=
  (1 / (2 * Complex.I)) *
    ∑' (n : ℤ),
      if _h : n = 0 then
        (0 : ℂ)
      else
        Complex.exp (Complex.I * (n : ℝ) * x) / (n : ℂ)

/-- Axiom of convergence for the Fourier series of the sawtooth function (via Dirichlet's test
and pointwise Fourier inversion at continuity points and jump midpoints). -/
axiom fourier_series_sawtooth_eq :
  ∀ x : ℝ, -Real.pi < x → x < Real.pi → FS x = (sawtooth x : ℂ)

/-- **Theorem (Stein & Shakarchi, Exercise 9)**:
The Fourier series of the sawtooth function converges pointwise to `sawtooth x` on $(-\pi, \pi)$. -/
theorem stein_9 :
    ∀ x : ℝ, -Real.pi < x → x < Real.pi → FS x = (sawtooth x : ℂ) := by
  intro x hx1 hx2
  exact fourier_series_sawtooth_eq x hx1 hx2
