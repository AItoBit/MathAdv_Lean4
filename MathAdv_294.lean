import Mathlib

open CategoryTheory

theorem conjugation_trivial_iff_commutative
    (G : Type*) [Group G] :
    (∀ g x : G, g⁻¹ * x * g = x) ↔
      ∀ x y : G, x * y = y * x := by
  constructor

  · intro h x y

    have hxy :
        x⁻¹ * y * x = y :=
      h x y

    have h' :
        x * (x⁻¹ * y * x) = x * y := by
      rw [hxy]

    have h'' : y * x = x * y := by
      simpa [mul_assoc] using h'

    exact h''.symm

  · intro h g x

    have hg :
        x * g = g * x :=
      h x g

    calc
      g⁻¹ * x * g
          = g⁻¹ * (x * g) := by
              rw [mul_assoc]
      _ = g⁻¹ * (g * x) := by
              rw [hg]
      _ = x := by
              simp


theorem fundamentalGroup_conjugation_trivial_iff_abelian
    {X : Type*} [TopologicalSpace X] (x₀ : X) :
    (∀ g a : FundamentalGroup X x₀,
        g⁻¹ * a * g = a) ↔
      ∀ a b : FundamentalGroup X x₀,
        a * b = b * a := by
  exact conjugation_trivial_iff_commutative
    (FundamentalGroup X x₀)
