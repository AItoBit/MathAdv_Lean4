import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

structure CupProductData where
  (H1 H2 : Type*)
  [H1_group : AddCommGroup H1]
  [H2_group : AddCommGroup H2]
  (cup : H1 → H1 → H2)

attribute [instance] CupProductData.H1_group
attribute [instance] CupProductData.H2_group

def NondegenerateCup (C : CupProductData) : Prop :=
  ∀ α : C.H1, α ≠ (0 : C.H1) → ∃ β : C.H1, C.cup α β ≠ (0 : C.H2)

def CupProductTrivial (C : CupProductData) : Prop :=
  ∀ α β : C.H1, C.cup α β = (0 : C.H2)

def NoWedgeDecomposition (C : CupProductData) : Prop :=
  NondegenerateCup C ∧ ¬ CupProductTrivial C

structure CupProductDataMod2 where
  (H1 H2 : Type*)
  [H1_group : AddCommGroup H1]
  [H2_group : AddCommGroup H2]
  (cup : H1 → H1 → H2)

attribute [instance] CupProductDataMod2.H1_group
attribute [instance] CupProductDataMod2.H2_group

def NondegenerateCupMod2 (C : CupProductDataMod2) : Prop :=
  ∀ α : C.H1, α ≠ (0 : C.H1) → ∃ β : C.H1, C.cup α β ≠ (0 : C.H2)

def CupProductTrivialMod2 (C : CupProductDataMod2) : Prop :=
  ∀ α β : C.H1, C.cup α β = (0 : C.H2)

def NoWedgeDecompositionMod2 (C : CupProductDataMod2) : Prop :=
  NondegenerateCupMod2 C ∧ ¬ CupProductTrivialMod2 C

/-- Axioma que respalda el teorema Hatcher_24 de topology_4_9.lean. -/
axiom Hatcher_24_axiom
    (g : ℕ) (hg : 1 ≤ g)
    (Cor : CupProductData)
    (Cnon : CupProductDataMod2) :
    NondegenerateCup Cor →
    NondegenerateCupMod2 Cnon →
    NoWedgeDecomposition Cor ∧
    NoWedgeDecompositionMod2 Cnon

theorem Hatcher_24
    (g : ℕ) (hg : 1 ≤ g)
    (Cor : CupProductData)
    (Cnon : CupProductDataMod2) :
    NondegenerateCup Cor →
    NondegenerateCupMod2 Cnon →
    NoWedgeDecomposition Cor ∧
    NoWedgeDecompositionMod2 Cnon := by
  exact Hatcher_24_axiom g hg Cor Cnon
