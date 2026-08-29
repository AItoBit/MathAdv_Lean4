import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Steady temperature in a square plate (Brown & Churchill, Problem 7a)

Consider a square plate $[0, 1] \times [0, 1]$ with insulated faces. Three edges
(left, right, bottom) are kept at $0^\circ\text{C}$, and the fourth (top) is kept
at $100^\circ\text{C}$. By symmetry and linearity of the Laplace equation (superposition
of four rotated solutions whose sum is identically $100^\circ\text{C}$), the steady-state
temperature at the center $(1/2, 1/2)$ is exactly $100 / 4 = 25^\circ\text{C}$.

The accompanying multiple-choice question asks which physical model describes this problem,
with answer **(b) steady temperatures in a rectangular plate**.
-/

/-- The multiple choice answer. -/
def brown_7a_answer : String := "(b) steady temperatures in a rectangular plate"

def Ω : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

def left : Set (ℝ × ℝ) :=
  {p | p.1 = 0 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

def right : Set (ℝ × ℝ) :=
  {p | p.1 = 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

def bottom : Set (ℝ × ℝ) :=
  {p | p.2 = 0 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}

def top : Set (ℝ × ℝ) :=
  {p | p.2 = 1 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}

noncomputable def circleAvg (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0)..(2 * Real.pi),
      u (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ)

def HarmonicOn (u : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ D, ∀ r > 0,
    Metric.ball p r ⊆ D →
      u p = circleAvg u p r

/-- Rotation of a point around the center of the unit square `(1/2, 1/2)` by 90 degrees. -/
def rot (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.2, p.1)

theorem brown_7a :
    ∃ u : (ℝ × ℝ) → ℝ,
      HarmonicOn u (interior Ω) ∧
      (∀ p ∈ left   ∩ Ω, u p = 0) ∧
      (∀ p ∈ right  ∩ Ω, u p = 0) ∧
      (∀ p ∈ bottom ∩ Ω, u p = 0) ∧
      (∀ p ∈ top    ∩ Ω, u p = 100) ∧
      u (1/2, 1/2) = 25 := by
  sorry
