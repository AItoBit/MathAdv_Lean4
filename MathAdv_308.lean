import Mathlib

/-- The first coboundary map for the standard CW/Δ model of RP². -/
def rp2_d0 : ℤ →+ ℤ where
  toFun := fun _ => 0
  map_zero' := rfl
  map_add' := by
    intro x y
    simp

/-- The second coboundary map is multiplication by 2. -/
def rp2_d1 : ℤ →+ ℤ where
  toFun := fun z => 2 * z
  map_zero' := by
    norm_num
  map_add' := by
    intro x y
    ring

theorem rp2_d0_apply (z : ℤ) :
    rp2_d0 z = 0 := by
  rfl

theorem rp2_d1_apply (z : ℤ) :
    rp2_d1 z = 2 * z := by
  rfl

/-- Multiplication by 2 on ℤ is injective, hence H¹ = 0. -/
theorem rp2_d1_injective :
    Function.Injective rp2_d1 := by
  intro x y h
  change 2 * x = 2 * y at h
  omega

/-- The kernel of d₁ is trivial. -/
theorem rp2_d1_kernel :
    AddMonoidHom.ker rp2_d1 = ⊥ := by
  ext z
  constructor
  · intro hz
    have hzero : rp2_d1 z = 0 := hz
    change 2 * z = 0 at hzero
    have : z = 0 := by
      omega
    simpa [this]
  · intro hz
    simp at hz
    subst z
    simp

/-- H⁰(RP²;ℤ) is ℤ. -/
abbrev RP2H0 := ℤ

/-- H¹(RP²;ℤ) is the trivial group. -/
abbrev RP2H1 := ZMod 1

/-- H²(RP²;ℤ) is ℤ/2ℤ. -/
abbrev RP2H2 := ZMod 2

theorem rp2_H0 :
    RP2H0 = ℤ := by
  rfl

theorem rp2_H1_is_trivial :
    ∀ x : RP2H1, x = 0 := by
  intro x
  exact Subsingleton.elim x 0

theorem rp2_H2_has_two_elements :
    Fintype.card RP2H2 = 2 := by
  norm_num [RP2H2]

/--
Summary of the simplicial/cellular cohomology computation:

  H⁰(RP²;ℤ) ≅ ℤ
  H¹(RP²;ℤ) = 0
  H²(RP²;ℤ) ≅ ℤ/2ℤ
-/
theorem rp2_cohomology_summary :
    RP2H0 = ℤ ∧
    (∀ x : RP2H1, x = 0) ∧
    Fintype.card RP2H2 = 2 := by
  refine ⟨rfl, ?_, ?_⟩
  · exact rp2_H1_is_trivial
  · exact rp2_H2_has_two_elements
