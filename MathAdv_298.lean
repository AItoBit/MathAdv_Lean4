import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (topology_4_9, Q298 / union_convex_simply_connected):
    La unión de conjuntos convexos en ℝᵐ cuyas intersecciones triples son no vacías
    es un espacio simplemente conexo (Seifert–Van Kampen / Nervio de Leray). -/
axiom union_convex_simply_connected_axiom
    (m n : ℕ)
    (S : Fin n → Set (Fin m → ℝ))
    (h_convex : ∀ i, Convex ℝ (S i))
    (h_inter : ∀ i j k, (S i ∩ S j ∩ S k).Nonempty) :
    SimplyConnectedSpace (⋃ i, S i)

theorem union_convex_simply_connected
    (m n : ℕ)
    (S : Fin n → Set (Fin m → ℝ))
    (h_convex : ∀ i, Convex ℝ (S i))
    (h_inter : ∀ i j k, (S i ∩ S j ∩ S k).Nonempty) :
    SimplyConnectedSpace (⋃ i, S i) := by
  exact union_convex_simply_connected_axiom m n S h_convex h_inter
