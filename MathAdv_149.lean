import Mathlib

open scoped Real
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- A unit-speed curve in ℝ³. -/
def UnitSpeed (γ : ℝ → R3) : Prop :=
  ∀ t, ‖deriv γ t‖ = 1

/-- Curvature κ(t) of a unit-speed curve. -/
noncomputable def curvature (γ : ℝ → R3) (t : ℝ) : ℝ :=
  ‖deriv (deriv γ) t‖

/-- Standard 3D cross product on `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def crossProduct3D (u v : R3) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![
    u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0
  ]

/-- Torsion τ(t) of a space curve. -/
noncomputable def torsion (γ : ℝ → R3) (t : ℝ) : ℝ :=
  let γ₁ : R3 := deriv γ t
  let γ₂ : R3 := deriv (deriv γ) t
  let γ₃ : R3 := deriv (deriv (deriv γ)) t
  let c : R3 := crossProduct3D γ₁ γ₂
  @inner ℝ R3 _ c γ₃ / (‖c‖ ^ 2)

/-- Standard circular helix with curvature κ and torsion τ. -/
noncomputable def circularHelix (κ τ : ℝ) : ℝ → R3 :=
  fun t =>
    let ω := Real.sqrt (κ ^ 2 + τ ^ 2)
    let r := κ / (κ ^ 2 + τ ^ 2)
    let c := τ / (κ ^ 2 + τ ^ 2)
    (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![
      r * Real.cos (ω * t),
      r * Real.sin (ω * t),
      c * t
    ]

/-- **Pressley, Exercise 2.3.2.**
Every curve in ℝ³ with constant curvature `κ > 0` and constant torsion `τ` is a
circular helix up to a rigid motion (isometry `A` and translation `v`). -/
theorem Pressley_2_3_2
    (γ : ℝ → R3)
    (κ τ : ℝ)
    (_hC3 : ContDiff ℝ 3 γ)
    (_h_unit : UnitSpeed γ)
    (_hκ : ∀ t, curvature γ t = κ)
    (_hτ : ∀ t, torsion γ t = τ)
    (_hκ_pos : 0 < κ) :
    ∃ (A : R3 ≃ₗᵢ[ℝ] R3) (v : R3),
      (∀ t, A (γ t) + v = circularHelix κ τ t) := by
  sorry
