import Mathlib

/-!
# A nonconstant complex polynomial is surjective

Given a polynomial `P : ℂ[X]` of positive degree, the evaluation map `z ↦ P(z)` is
surjective. This is a consequence of the fundamental theorem of algebra: for any
`w : ℂ` the polynomial `P - C w` is again nonconstant, hence has a root, since `ℂ`
is algebraically closed.
-/

/-- Subtracting a constant from a nonconstant polynomial leaves it nonconstant:
its degree is still positive. -/
theorem degree_sub_C_pos_of_natDegree_ne_zero
    (P : Polynomial ℂ) (hP : P.natDegree ≠ 0) (w : ℂ) :
    0 < (P - Polynomial.C w).degree := by
  have h : (P - Polynomial.C w).natDegree ≠ 0 := by simpa using hP
  exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)

/-- A nonconstant polynomial over `ℂ` is onto (fundamental theorem of algebra). -/
theorem question_9
    (P : Polynomial ℂ)
    (hP : P.natDegree ≠ 0) :
    Function.Surjective (fun z : ℂ => P.eval z) := by
  intro w
  obtain ⟨z, hz⟩ := Complex.exists_root (degree_sub_C_pos_of_natDegree_ne_zero P hP w)
  exact ⟨z, by simpa [Polynomial.IsRoot, sub_eq_zero] using hz⟩
