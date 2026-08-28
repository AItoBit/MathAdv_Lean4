import Mathlib

open Equiv

namespace RetosMatematicos

variable {G : Type*} [CommGroup G]

lemma negOne_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg Units.val h
  norm_num at h'

/-- For an involution `a : G`, the homomorphism `ℤˣ →* G` sending `-1 ↦ a`. -/
def signHom (a : G) (ha : a ^ (2 : ℕ) = 1) : ℤˣ →* G where
  toFun u := if u = 1 then 1 else a
  map_one' := by simp
  map_mul' u v := by
    have ha' : a * a = 1 := by rw [← pow_two]; exact ha
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;>
        simp [ha']

/-- The homomorphism `S₃ →* G` attached to an involution `a : G`. -/
def permHom (a : G) (ha : a ^ (2 : ℕ) = 1) : Equiv.Perm (Fin 3) →* G :=
  (signHom a ha).comp Equiv.Perm.sign

@[simp] lemma permHom_apply (a : G) (ha : a ^ (2 : ℕ) = 1) (σ : Equiv.Perm (Fin 3)) :
    permHom a ha σ = if Equiv.Perm.sign σ = 1 then 1 else a := rfl

lemma permHom_swap (a : G) (ha : a ^ (2 : ℕ) = 1) {x y : Fin 3} (h : x ≠ y) :
    permHom a ha (Equiv.swap x y) = a := by
  simp [permHom_apply, Equiv.Perm.sign_swap h, negOne_ne_one]

lemma swap_sq (F : Equiv.Perm (Fin 3) →* G) : (F (Equiv.swap 0 1)) ^ (2 : ℕ) = 1 := by
  rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]

/-- Every hom `S₃ →* G` into an abelian group is determined by its value on `swap 0 1`. -/
lemma eq_permHom (F : Equiv.Perm (Fin 3) →* G) (σ : Equiv.Perm (Fin 3)) :
    F σ = permHom (F (Equiv.swap 0 1)) (swap_sq F) σ := by
  have conj : ∀ c s : Equiv.Perm (Fin 3), F (c * s * c⁻¹) = F s := by
    intro c s
    simp only [map_mul, map_inv]
    rw [mul_comm (F c) (F s), mul_inv_cancel_right]
  have key : ∀ x y : Fin 3, x ≠ y →
      ∃ c : Equiv.Perm (Fin 3), Equiv.swap x y = c * Equiv.swap 0 1 * c⁻¹ := by decide
  have hF : ∀ x y : Fin 3, x ≠ y → F (Equiv.swap x y) = F (Equiv.swap 0 1) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := key x y hxy
    rw [hc, conj]
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · simp
  · intro g x y hxy hg
    rw [map_mul, map_mul, hg, hF x y hxy, permHom_swap _ _ hxy]

theorem Gallian_8
    (G : Type*) [CommGroup G] :
    Nonempty ({a : G // a ^ (2 : ℕ) = (1 : G)} ≃ ((Equiv.Perm (Fin 3)) →* G)) :=
  ⟨{ toFun := fun a => permHom a.1 a.2
     invFun := fun F => ⟨F (Equiv.swap 0 1), swap_sq F⟩
     left_inv := fun a =>
       Subtype.ext (permHom_swap a.1 a.2 (show (0 : Fin 3) ≠ 1 by decide))
     right_inv := fun F => MonoidHom.ext fun σ => (eq_permHom F σ).symm }⟩

end RetosMatematicos
