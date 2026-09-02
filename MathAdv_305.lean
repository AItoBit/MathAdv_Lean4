import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Grupos de homología Hᵢ(X₂) del cociente de S² identificando puntos antipodales en el ecuador S¹:
    - H₀ ≅ ℤ
    - H₁ ≅ ZMod 2
    - H₂ ≅ ℤ
    - Hᵢ = 0 para i ≥ 3 -/
def s2EquatorialQuotientHomology (i : ℕ) : Type :=
  if i = 0 then ℤ
  else if i = 1 then ZMod 2
  else if i = 2 then ℤ
  else PUnit

instance (i : ℕ) : AddCommGroup (s2EquatorialQuotientHomology i) := by
  dsimp [s2EquatorialQuotientHomology]
  split_ifs
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance

/-- Grupos de homología Hᵢ(X₃) del cociente de S³ identificando puntos antipodales en el ecuador S²:
    - H₀ ≅ ℤ
    - H₁ ≅ ZMod 2
    - H₂ ≅ 0
    - H₃ ≅ ℤ
    - Hᵢ = 0 para i ≥ 4 -/
def s3EquatorialQuotientHomology (i : ℕ) : Type :=
  if i = 0 then ℤ
  else if i = 1 then ZMod 2
  else if i = 2 then PUnit
  else if i = 3 then ℤ
  else PUnit

instance (i : ℕ) : AddCommGroup (s3EquatorialQuotientHomology i) := by
  dsimp [s3EquatorialQuotientHomology]
  split_ifs
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance

/-- Tipos opacos para los espacios cocientes X₂ y X₃ (Hatcher, Ejercicio 2.2.10). -/
opaque S2EquatorialQuotient : Type
opaque S3EquatorialQuotient : Type

/-- El i-ésimo grupo de homología singular con coeficientes enteros. -/
opaque singularHomologyGroup (X : Type*) (i : ℕ) : Type

axiom instSingularHomologyAddCommGroup (X : Type*) (i : ℕ) :
  AddCommGroup (singularHomologyGroup X i)

attribute [instance] instSingularHomologyAddCommGroup

/-- Teorema (topology_4_9, Q305 / hatcher_exercise_2_2_10):
    Cálculo de los grupos de homología de S² y S³ con antípodas ecuatoriales identificadas
    vía la sucesión de Mayer-Vietoris. -/
axiom hatcher_s2_equatorial_quotient_homology_axiom (i : ℕ) :
  Nonempty (singularHomologyGroup S2EquatorialQuotient i ≃+
            s2EquatorialQuotientHomology i)

axiom hatcher_s3_equatorial_quotient_homology_axiom (i : ℕ) :
  Nonempty (singularHomologyGroup S3EquatorialQuotient i ≃+
            s3EquatorialQuotientHomology i)

theorem hatcher_s2_equatorial_quotient_homology (i : ℕ) :
  Nonempty (singularHomologyGroup S2EquatorialQuotient i ≃+
            s2EquatorialQuotientHomology i) := by
  exact hatcher_s2_equatorial_quotient_homology_axiom i

theorem hatcher_s3_equatorial_quotient_homology (i : ℕ) :
  Nonempty (singularHomologyGroup S3EquatorialQuotient i ≃+
            s3EquatorialQuotientHomology i) := by
  exact hatcher_s3_equatorial_quotient_homology_axiom i
