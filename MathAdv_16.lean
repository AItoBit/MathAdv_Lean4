import Mathlib

/-!
# A surjective homomorphism onto a cyclic group need not have cyclic domain

The statement "if `f : G → H` is a surjective homomorphism, then `H` cyclic implies
`G` cyclic" is false.  A counterexample is given by the symmetric group `S₃`
(realized as `Equiv.Perm (Fin 3)`) mapping onto the trivial group `PUnit`:
the map is surjective, the trivial group is cyclic, but `S₃` is not cyclic since
it is not commutative.  (Universe-polymorphic versions of `S₃` are obtained via
`ULift`.)
-/

/-- `Equiv.Perm (Fin 3)` (the symmetric group `S₃`) is not cyclic:
a cyclic group is commutative, but the transpositions `(0 1)` and `(1 2)` do not commute. -/
theorem not_isCyclic_perm_fin_three : ¬ IsCyclic (Equiv.Perm (Fin 3)) := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_generator
  obtain ⟨m, hm⟩ := hg (Equiv.swap (0 : Fin 3) 1)
  obtain ⟨n, hn⟩ := hg (Equiv.swap (1 : Fin 3) 2)
  have key : Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2
      = Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  revert key
  decide

/-- Any universe lift of `S₃` is not cyclic either. -/
theorem not_isCyclic_ulift_perm_fin_three :
    ¬ IsCyclic (ULift.{u} (Equiv.Perm (Fin 3))) := fun h =>
  not_isCyclic_perm_fin_three
    (isCyclic_of_surjective (hH := h) (MulEquiv.ulift (α := Equiv.Perm (Fin 3))).toMonoidHom
      MulEquiv.ulift.surjective)

/-- The statement "a surjective homomorphism onto a cyclic group has cyclic domain" is false:
the projection of `S₃` onto the trivial group is a surjective homomorphism onto a cyclic
group, yet `S₃` is not cyclic. -/
theorem Gallian_17 :
  ∃ (G H : Type*) (_ : Group G) (_ : Group H) (f : G →* H),
      Function.Surjective f ∧ IsCyclic H ∧ ¬ IsCyclic G := by
  refine ⟨ULift (Equiv.Perm (Fin 3)), PUnit, inferInstance, inferInstance, 1, ?_, ?_,
    not_isCyclic_ulift_perm_fin_three⟩
  · intro y
    exact ⟨1, Subsingleton.elim _ _⟩
  · infer_instance
