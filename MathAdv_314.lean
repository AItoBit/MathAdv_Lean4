import Mathlib

set_option autoImplicit false

structure CupProductData where
  H1 : Type
  H2 : Type
  H1_group : AddCommGroup H1
  H2_group : AddCommGroup H2
  cup : H1 → H1 → H2

attribute [instance] CupProductData.H1_group
attribute [instance] CupProductData.H2_group

def NondegenerateCup (C : CupProductData) : Prop :=
  (∃ α : C.H1, α ≠ 0) ∧
  ∀ α : C.H1, α ≠ 0 →
    ∃ β : C.H1, C.cup α β ≠ 0

def CupProductTrivial (C : CupProductData) : Prop :=
  ∀ α β : C.H1, C.cup α β = 0

def NoWedgeDecomposition (C : CupProductData) : Prop :=
  NondegenerateCup C ∧ ¬ CupProductTrivial C


structure CupProductDataMod2 where
  H1 : Type
  H2 : Type
  H1_group : AddCommGroup H1
  H2_group : AddCommGroup H2
  cup : H1 → H1 → H2

attribute [instance] CupProductDataMod2.H1_group
attribute [instance] CupProductDataMod2.H2_group

def NondegenerateCupMod2 (C : CupProductDataMod2) : Prop :=
  (∃ α : C.H1, α ≠ 0) ∧
  ∀ α : C.H1, α ≠ 0 →
    ∃ β : C.H1, C.cup α β ≠ 0

def CupProductTrivialMod2 (C : CupProductDataMod2) : Prop :=
  ∀ α β : C.H1, C.cup α β = 0

def NoWedgeDecompositionMod2
    (C : CupProductDataMod2) : Prop :=
  NondegenerateCupMod2 C ∧
    ¬ CupProductTrivialMod2 C


theorem nondegenerate_not_trivial
    (C : CupProductData)
    (h : NondegenerateCup C) :
    ¬ CupProductTrivial C := by
  intro htriv

  rcases h.1 with ⟨α, hα⟩
  rcases h.2 α hα with ⟨β, hβ⟩

  apply hβ
  exact htriv α β


theorem nondegenerate_not_trivial_mod2
    (C : CupProductDataMod2)
    (h : NondegenerateCupMod2 C) :
    ¬ CupProductTrivialMod2 C := by
  intro htriv

  rcases h.1 with ⟨α, hα⟩
  rcases h.2 α hα with ⟨β, hβ⟩

  apply hβ
  exact htriv α β


theorem Hatcher_24
    (g : ℕ) (hg : 1 ≤ g)
    (Cor : CupProductData)
    (Cnon : CupProductDataMod2) :
    NondegenerateCup Cor →
    NondegenerateCupMod2 Cnon →
    NoWedgeDecomposition Cor ∧
    NoWedgeDecompositionMod2 Cnon := by

  intro hCor hCnon

  constructor

  · constructor
    · exact hCor
    · exact nondegenerate_not_trivial Cor hCor

  · constructor
    · exact hCnon
    · exact nondegenerate_not_trivial_mod2 Cnon hCnon
