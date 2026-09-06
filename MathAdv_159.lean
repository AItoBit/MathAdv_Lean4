import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The Lie derivative along `f • X`

We show that for a differential form `ω`, a vector field `X` and a smooth function `f`,
`𝓛_{fX} ω = f 𝓛_X ω + df ∧ ι_X ω`.

Mathlib does not (at the time of writing) contain the Lie derivative of a differential form
along a vector field, so we work in the standard algebraic axiomatisation of the Cartan
calculus, which is exactly the structure the informal proof uses:

* `A` is the (graded) algebra of differential forms, with product the wedge product;
* `C` is the ring of smooth functions, acting on forms and on vector fields;
* `d : A → A` is the exterior derivative; for a *function* `f` we write `dOf d f` for `df`;
* `iota X : A → A` is the interior product (contraction) with the vector field `X`;
* the Lie derivative is *defined* by **Cartan's magic formula** `𝓛_X = d ∘ ι_X + ι_X ∘ d`
  (this is the theorem which, per the accompanying multiple choice question, is the useful
  one here: answer **(b)**).

The only two properties needed are:

* the Leibniz rule for `d` against a degree-zero factor: `d (f • ω) = df ∧ ω + f • dω`;
* `C`-linearity of the contraction in the vector field: `ι_{f X} = f ι_X`.

Finally we record that the completely unstructured statement — with `lieDeriv`, `d`, `iota`
and `wedge` arbitrary functions subject to no axioms whatsoever — is *false*; see
`lieDeriv_smul_vectorField_unstructured_false` at the end of the file.
-/

namespace CartanCalculus

variable {C A V : Type*} [CommRing C] [Ring A] [Algebra C A]
  [AddCommGroup V] [Module C V]

/-- The exterior derivative of a smooth function `f`, viewed as a `1`-form:
`dOf d f = d f` where `f` is regarded as a degree-zero element of the algebra of forms. -/
def dOf (d : A → A) (f : C) : A := d (algebraMap C A f)

/-- The Lie derivative along a vector field, defined by Cartan's magic formula
`𝓛_X ω = d (ι_X ω) + ι_X (d ω)`. -/
def lieDeriv (d : A → A) (iota : V → A → A) (X : V) (ω : A) : A :=
  d (iota X ω) + iota X (d ω)

/-- **`𝓛_{fX} ω = f 𝓛_X ω + df ∧ ι_X ω`.**

Here `d` is the exterior derivative, assumed to satisfy the Leibniz rule `hd` against a
degree-zero (i.e. function) factor, and `iota` is the interior product, assumed to be
linear over functions in the vector field slot (`hiota`).  The Lie derivative is given by
Cartan's magic formula, and the wedge product is the multiplication of the algebra of forms. -/
theorem lieDeriv_smul_vectorField (d : A → A) (iota : V → A → A)
    (hd : ∀ (f : C) (ω : A), d (f • ω) = dOf d f * ω + f • d ω)
    (hiota : ∀ (f : C) (X : V) (ω : A), iota (f • X) ω = f • iota X ω)
    (f : C) (X : V) (ω : A) :
    lieDeriv d iota (f • X) ω
      = f • lieDeriv d iota X ω + dOf d f * iota X ω := by
  simp only [lieDeriv, hiota, hd, smul_add]
  abel

end CartanCalculus

/-- The statement of the problem with *no* relations imposed between the Lie derivative,
the exterior derivative, the interior product and the wedge product is false: nothing then
forces the three operations to interact at all.

(Original formulation, kept for the record; it is refuted by taking every type to be `ℕ`,
`lieDeriv X ω = ω`, and all of `d`, `iota`, `wedge` equal to zero, with `f = 0`, `ω = 1`.)
-/
theorem lieDeriv_smul_vectorField_unstructured_false :
    ¬ (∀ (k : ℕ) (F : Type) (VF : Type) (Ω : ℕ → Type)
        [CommSemiring F] [AddCommMonoid VF] [Module F VF]
        [∀ n, AddCommMonoid (Ω n)] [∀ n, Module F (Ω n)]
        (lieDeriv : VF → Ω k → Ω k) (d : F → Ω 1) (iota : VF → Ω k → Ω (k - 1))
        (wedge : Ω 1 → Ω (k - 1) → Ω k) (f : F) (X : VF) (ω : Ω k),
        lieDeriv (f • X) ω = f • lieDeriv X ω + wedge (d f) (iota X ω)) := by
  intro h
  have := h 0 ℕ ℕ (fun _ => ℕ) (fun _ ω => ω) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) 0 0 1
  simp at this

 
