import Mathlib

namespace RetosMatematicos

universe u

abbrev V := ZMod 2 × ZMod 2

/-- First projection, as a homomorphism out of the lifted Klein four-group. -/
def f₁ : ULift.{u} V →+ ZMod 2 where
  toFun x := x.down.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Second projection. -/
def f₂ : ULift.{u} V →+ ZMod 2 where
  toFun x := x.down.2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma f₁_apply (x : ULift.{u} V) : f₁ x = x.down.1 := rfl
@[simp] lemma f₂_apply (x : ULift.{u} V) : f₂ x = x.down.2 := rfl

/-- `{(0, b)}`. -/
def K₁ : AddSubgroup (ULift.{u} V) := (f₁ : ULift.{u} V →+ ZMod 2).ker
/-- `{(a, 0)}`. -/
def K₂ : AddSubgroup (ULift.{u} V) := (f₂ : ULift.{u} V →+ ZMod 2).ker
/-- The diagonal `{(a, a)}`, as the kernel of the difference of the projections. -/
def K₃ : AddSubgroup (ULift.{u} V) := (f₁ - f₂ : ULift.{u} V →+ ZMod 2).ker

@[simp] lemma mem_K₁ (x : ULift.{u} V) : x ∈ K₁ ↔ x.down.1 = 0 := by
  simp [K₁, AddMonoidHom.mem_ker]

@[simp] lemma mem_K₂ (x : ULift.{u} V) : x ∈ K₂ ↔ x.down.2 = 0 := by
  simp [K₂, AddMonoidHom.mem_ker]

@[simp] lemma mem_K₃ (x : ULift.{u} V) : x ∈ K₃ ↔ x.down.1 = x.down.2 := by
  simp [K₃, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]

lemma K₁_ne_top : (K₁ : AddSubgroup (ULift.{u} V)) ≠ ⊤ := by
  intro h
  have hx : (ULift.up ((1 : ZMod 2), (0 : ZMod 2)) : ULift.{u} V) ∈ K₁ := by
    rw [h]; exact AddSubgroup.mem_top _
  rw [mem_K₁] at hx
  exact absurd hx (by decide)

lemma K₂_ne_top : (K₂ : AddSubgroup (ULift.{u} V)) ≠ ⊤ := by
  intro h
  have hx : (ULift.up ((0 : ZMod 2), (1 : ZMod 2)) : ULift.{u} V) ∈ K₂ := by
    rw [h]; exact AddSubgroup.mem_top _
  rw [mem_K₂] at hx
  exact absurd hx (by decide)

lemma K₃_ne_top : (K₃ : AddSubgroup (ULift.{u} V)) ≠ ⊤ := by
  intro h
  have hx : (ULift.up ((1 : ZMod 2), (0 : ZMod 2)) : ULift.{u} V) ∈ K₃ := by
    rw [h]; exact AddSubgroup.mem_top _
  rw [mem_K₃] at hx
  exact absurd hx (by decide)

lemma K_union :
    ((K₁ : AddSubgroup (ULift.{u} V)) : Set (ULift.{u} V)) ∪ (K₂ : Set (ULift.{u} V))
      ∪ (K₃ : Set (ULift.{u} V)) = Set.univ := by
  ext x
  obtain ⟨y⟩ := x
  simp only [Set.mem_union, SetLike.mem_coe, Set.mem_univ, iff_true,
    mem_K₁, mem_K₂, mem_K₃]
  revert y
  decide

theorem Gallian_10 :
    ∃ (G : Type*) (_ : AddGroup G) (H₁ H₂ H₃ : AddSubgroup G),
      H₁ ≠ ⊤ ∧ H₂ ≠ ⊤ ∧ H₃ ≠ ⊤ ∧
      ((H₁ : Set G) ∪ (H₂ : Set G) ∪ (H₃ : Set G) = Set.univ) :=
  ⟨ULift V, inferInstance, K₁, K₂, K₃, K₁_ne_top, K₂_ne_top, K₃_ne_top, K_union⟩

end RetosMatematicos
