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
# Distributing `k` forints among `n` persons (Lovász, Combinatorial Problems and Exercises 4.9)

A distribution of `k` (identical) forints to `n` persons is a function `f : Fin n → ℕ`
with `∑ i, f i = k`.  The classical "stars and bars" count says that there are
`(n + k - 1).choose (n - 1)` such distributions.

Answer to the accompanying multiple-choice question: **(d) the Pólya–Redfield method**.
-/

/-- Distributions of `k` units among `n` persons correspond bijectively to multisets of
size `k` over `Fin n`: a multiset is sent to its multiplicity function. -/
noncomputable def symEquivSumFin (n k : ℕ) :
    Sym (Fin n) k ≃ {f : Fin n → ℕ // ∑ i, f i = k} :=
  Equiv.subtypeEquiv (Multiset.toFinsupp.toEquiv.trans Finsupp.equivFunOnFinite)
    (by
      intro m
      have hcount : ∑ i : Fin n, m.count i = Multiset.card m :=
        Multiset.sum_count_eq_card (by intro a _; exact Finset.mem_univ a)
      simp [Multiset.toFinsupp_apply, hcount])

/-- The number of ways to distribute `k` forints among `n` persons is `(n + k - 1).choose (n - 1)`,
stated as the existence of a bijection with `Fin ((n + k - 1).choose (n - 1))`. -/
theorem Lovasz_16 (n k : ℕ) (hn : 0 < n) :
  Nonempty
    ({ f : Fin n → ℕ // (∑ i : Fin n, f i) = k } ≃
     Fin (Nat.choose (n + k - 1) (n - 1))) := by
  classical
  let _inst : Fintype { f : Fin n → ℕ // (∑ i : Fin n, f i) = k } :=
    Fintype.ofEquiv _ (symEquivSumFin n k)
  have hc : Fintype.card { f : Fin n → ℕ // (∑ i : Fin n, f i) = k }
      = Nat.choose (n + k - 1) (n - 1) := by
    rw [Fintype.card_congr (symEquivSumFin n k).symm, Sym.card_sym_eq_choose,
      Fintype.card_fin]
    exact Nat.choose_symm_of_eq_add (by omega)
  exact ⟨Fintype.equivFinOfCardEq hc⟩
