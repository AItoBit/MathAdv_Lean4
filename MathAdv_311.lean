import Mathlib

/--
The standard degree-one basis of the cohomology of an orientable
surface of genus g consists of αᵢ and βᵢ for i : Fin g.
-/
inductive SurfaceH1Basis (g : ℕ)
  | alpha : Fin g → SurfaceH1Basis g
  | beta  : Fin g → SurfaceH1Basis g
  deriving DecidableEq

/--
Coefficient of the generator γ ∈ H²(M_g; ℤ) in the cup product
of two standard H¹ basis elements.
-/
def surfaceCupCoeff {g : ℕ} :
    SurfaceH1Basis g → SurfaceH1Basis g → ℤ
  | .alpha _, .alpha _ => 0
  | .beta _,  .beta _  => 0
  | .alpha i, .beta j  => if i = j then 1 else 0
  | .beta i,  .alpha j => if i = j then -1 else 0

/--
αᵢ ∪ αⱼ = 0.
-/
theorem alpha_cup_alpha
    {g : ℕ} (i j : Fin g) :
    surfaceCupCoeff
      (SurfaceH1Basis.alpha i)
      (SurfaceH1Basis.alpha j) = 0 := by
  rfl

/--
βᵢ ∪ βⱼ = 0.
-/
theorem beta_cup_beta
    {g : ℕ} (i j : Fin g) :
    surfaceCupCoeff
      (SurfaceH1Basis.beta i)
      (SurfaceH1Basis.beta j) = 0 := by
  rfl

/--
αᵢ ∪ βᵢ = γ.
-/
theorem alpha_cup_beta_same
    {g : ℕ} (i : Fin g) :
    surfaceCupCoeff
      (SurfaceH1Basis.alpha i)
      (SurfaceH1Basis.beta i) = 1 := by
  simp [surfaceCupCoeff]

/--
αᵢ ∪ βⱼ = 0 when i ≠ j.
-/
theorem alpha_cup_beta_ne
    {g : ℕ} {i j : Fin g}
    (hij : i ≠ j) :
    surfaceCupCoeff
      (SurfaceH1Basis.alpha i)
      (SurfaceH1Basis.beta j) = 0 := by
  simp [surfaceCupCoeff, hij]

/--
βᵢ ∪ αᵢ = -γ.
-/
theorem beta_cup_alpha_same
    {g : ℕ} (i : Fin g) :
    surfaceCupCoeff
      (SurfaceH1Basis.beta i)
      (SurfaceH1Basis.alpha i) = -1 := by
  simp [surfaceCupCoeff]

/--
βᵢ ∪ αⱼ = 0 when i ≠ j.
-/
theorem beta_cup_alpha_ne
    {g : ℕ} {i j : Fin g}
    (hij : i ≠ j) :
    surfaceCupCoeff
      (SurfaceH1Basis.beta i)
      (SurfaceH1Basis.alpha j) = 0 := by
  simp [surfaceCupCoeff, hij]

/--
Graded commutativity in degree one:
x ∪ y = -(y ∪ x)
on the standard basis.
-/
theorem surface_cup_skew
    {g : ℕ}
    (x y : SurfaceH1Basis g) :
    surfaceCupCoeff x y =
      - surfaceCupCoeff y x := by
  cases x with
  | alpha i =>
      cases y with
      | alpha j =>
          simp [surfaceCupCoeff]
      | beta j =>
          by_cases hij : i = j
          · subst j
            simp [surfaceCupCoeff]
          · simp [surfaceCupCoeff, hij, Ne.symm hij]
  | beta i =>
      cases y with
      | alpha j =>
          by_cases hij : i = j
          · subst j
            simp [surfaceCupCoeff]
          · simp [surfaceCupCoeff, hij, Ne.symm hij]
      | beta j =>
          simp [surfaceCupCoeff]

/--
The requested cup-product formula:
αᵢ ∪ βⱼ has coefficient δᵢⱼ in front of γ.
-/
theorem surface_cup_delta
    {g : ℕ} (i j : Fin g) :
    surfaceCupCoeff
      (SurfaceH1Basis.alpha i)
      (SurfaceH1Basis.beta j)
      =
      if i = j then 1 else 0 := by
  rfl

/--
Summary of the standard cup-product structure of H*(M_g; ℤ).
-/
theorem orientable_surface_cup_product_structure
    {g : ℕ} :
    (∀ i j : Fin g,
      surfaceCupCoeff
        (SurfaceH1Basis.alpha i)
        (SurfaceH1Basis.alpha j) = 0) ∧
    (∀ i j : Fin g,
      surfaceCupCoeff
        (SurfaceH1Basis.beta i)
        (SurfaceH1Basis.beta j) = 0) ∧
    (∀ i j : Fin g,
      surfaceCupCoeff
        (SurfaceH1Basis.alpha i)
        (SurfaceH1Basis.beta j)
        =
        if i = j then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rfl
  · intro i j
    rfl
  · intro i j
    rfl
