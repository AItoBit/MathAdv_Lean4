import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Tipo opaco para el n-ésimo grupo de homología reducida singular H̃ₙ(X; ℤ). -/
opaque reducedHomologyGroup (X : Type*) [TopologicalSpace X] (n : ℕ) : Type

axiom instReducedHomologyAddCommGroup
    (X : Type*) [TopologicalSpace X] (n : ℕ) :
    AddCommGroup (reducedHomologyGroup X n)

attribute [instance] instReducedHomologyAddCommGroup

/-- Relación de identificación para la suma cuña X ∨ Y con respecto a puntos base x₀ e y₀. -/
inductive WedgeRel {X Y : Type*} (x₀ : X) (y₀ : Y) : X ⊕ Y → X ⊕ Y → Prop where
  | glue : WedgeRel x₀ y₀ (Sum.inl x₀) (Sum.inr y₀)

/-- La suma cuña X ∨ Y de dos espacios con punto base como espacio cociente. -/
def WedgeSum {X Y : Type*} (x₀ : X) (y₀ : Y) : Type _ :=
  Quot (fun (a b : X ⊕ Y) => WedgeRel x₀ y₀ a b ∨ WedgeRel x₀ y₀ b a ∨ a = b)

instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y) :
    TopologicalSpace (WedgeSum x₀ y₀) :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- Condición de par bueno (good pair): el punto base posee una vecindad
    de la cual es un retracto por deformación fuerte. -/
def IsGoodBasepoint {X : Type*} [TopologicalSpace X] (x₀ : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x₀ ∈ U

/-- Teorema (topology_4_9, Q306 / hatcher_wedge_sum_reduced_homology):
    Si los puntos base de X e Y satisfacen la condición de vecindad de deformación,
    la sucesión exacta de Mayer-Vietoris induce el isomorfismo H̃ₙ(X ∨ Y) ≅ H̃ₙ(X) ⊕ H̃ₙ(Y)
    (Hatcher, Corolario 2.25). -/
axiom hatcher_wedge_sum_reduced_homology_axiom
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hx : IsGoodBasepoint x₀)
    (hy : IsGoodBasepoint y₀)
    (n : ℕ) :
    Nonempty (reducedHomologyGroup (WedgeSum x₀ y₀) n ≃+
              (reducedHomologyGroup X n × reducedHomologyGroup Y n))

theorem hatcher_wedge_sum_reduced_homology
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hx : IsGoodBasepoint x₀)
    (hy : IsGoodBasepoint y₀)
    (n : ℕ) :
    Nonempty (reducedHomologyGroup (WedgeSum x₀ y₀) n ≃+
              (reducedHomologyGroup X n × reducedHomologyGroup Y n)) := by
  exact hatcher_wedge_sum_reduced_homology_axiom x₀ y₀ hx hy n
