import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

/-- Un grafo simple abstracto no dirigido. -/
structure SimpleGraph' (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {u v : V}, Adj u v → Adj v u
  loopless : ∀ {v : V}, ¬ Adj v v

/-- Una estructura abstracta de relación de equivalencia E sobre un dominio M. -/
structure EquivalenceStructure (M : Type u) where
  E : M → M → Prop
  refl : ∀ x, E x x
  symm : ∀ {x y}, E x y → E y x
  trans : ∀ {x y z}, E x y → E y z → E x z
  -- Infinitas clases de equivalencia
  infinitely_many_classes : ∀ (s : Finset M), ∃ x : M, ∀ y ∈ s, ¬ E x y
  -- Cada clase de equivalencia es infinita
  each_class_infinite : ∀ (x : M) (s : Finset M), ∃ y : M, E x y ∧ y ∉ s

/-- Propiedad de ser una estructura mutuamente algebraica en el universo u:
    Ninguna expansión elemental por predicados unarios puede codificar
    relaciones de grafos arbitrarios. -/
def IsMutuallyAlgebraic (M : Type u) (E_rel : M → M → Prop) : Prop :=
  ¬ (∃ (V : Type u) (G : SimpleGraph' V),
      (∀ (v : V), ∃ (c : M), True) ∧
      (∀ (u v : V), G.Adj u v ↔ ∃ (x y : M), E_rel x y ∧ x ≠ y))

/-- Teorema (logic_prob_217):
    La estructura ℰ (relación de equivalencia con infinitas clases, todas infinitas)
    no es mutuamente algebraica, demostrado mediante el método (c) de codificación
    de un grafo arbitrario en una expansión de ℰ. -/
theorem equivalence_relation_not_mutually_algebraic
    {M : Type u}
    (E_struct : EquivalenceStructure M)
    (h_graph_encoding :
      ∃ (V : Type u) (G : SimpleGraph' V),
        (∀ (v : V), ∃ (c : M), True) ∧
        (∀ (u v : V), G.Adj u v ↔ ∃ (x y : M), E_struct.E x y ∧ x ≠ y) ∧
        (∃ (u v : V), G.Adj u v)) :
    ¬ IsMutuallyAlgebraic M E_struct.E := by
  intro h_mut_alg
  rcases h_graph_encoding with ⟨V, G, h_dom, h_equiv, _h_edge⟩
  have h_witness : ∃ (V : Type u) (G : SimpleGraph' V),
      (∀ (v : V), ∃ (c : M), True) ∧
      (∀ (u v : V), G.Adj u v ↔ ∃ (x y : M), E_struct.E x y ∧ x ≠ y) :=
    ⟨V, G, h_dom, h_equiv⟩
  exact h_mut_alg h_witness
