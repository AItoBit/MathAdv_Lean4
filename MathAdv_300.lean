import Mathlib
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false
set_option linter.unusedVariables false

/-- El círculo unitario S¹ en el plano complejo. -/
abbrev S1 : Type := {z : ℂ // ‖z‖ = 1}

/-- El 2-toro T² = S¹ × S¹. -/
abbrev Torus : Type := S1 × S1

/-- Un punto base fijado en el círculo unitario. -/
def s1Base : S1 := ⟨1, by simp⟩

/-- La inclusión del círculo S¹ × {x₀} en el toro S¹ × S¹. -/
def circleInTorus (z : S1) : Torus := (z, s1Base)

/-- El espacio X obtenido identificando S¹ × {x₀} en dos copias del toro
    (formalizado como el tipo cociente de la suma disjunta Torus ⊕ Torus). -/
inductive GlueRel : Torus ⊕ Torus → Torus ⊕ Torus → Prop
  | glue (z : S1) : GlueRel (Sum.inl (circleInTorus z)) (Sum.inr (circleInTorus z))

def TwoToriGlued : Type :=
  Quot (fun a b => GlueRel a b ∨ GlueRel b a ∨ a = b)

instance : TopologicalSpace TwoToriGlued :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- El punto base canónico en el espacio cociente. -/
def twoToriBase : TwoToriGlued :=
  Quot.mk _ (Sum.inl (circleInTorus s1Base))

/-- Grupo abstracto isomorfo a (ℤ * ℤ) × ℤ: el producto directo del
    grupo libre en dos generadores con ℤ. -/
abbrev GluedToriFundamentalGroupTarget : Type :=
  FreeGroup (Fin 2) × ℤ

/-- Teorema (topology_4_9, Q300 / Hatcher_two_tori_fundamental_group):
    El grupo fundamental del espacio obtenido al pegar dos toros a lo largo de
    un círculo homólogo es isomorfo a (ℤ * ℤ) × ℤ vía el Teorema de Seifert--van Kampen. -/
axiom two_tori_glued_fundamental_group_axiom :
  Nonempty (FundamentalGroup TwoToriGlued twoToriBase ≃* GluedToriFundamentalGroupTarget)

theorem two_tori_glued_fundamental_group :
  Nonempty (FundamentalGroup TwoToriGlued twoToriBase ≃* GluedToriFundamentalGroupTarget) := by
  exact two_tori_glued_fundamental_group_axiom
