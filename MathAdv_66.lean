import Mathlib

/-!
# Lovász, Problem 15: the crosscut theorem for the atoms of a finite lattice

Let `V` be a finite lattice, `R` its set of atoms, `n = |R|`, and let `q l` be the number of
`l`-element subsets of `R` whose join is `⊤`. Then
`μ(⊥, ⊤) = ∑_{l = 0}^{n} (-1)^l q l`.

The main result is `Lovasz15.Lovasz_15`. The proof is a Möbius-inversion argument: writing `f x`
for the alternating count of the sets of atoms whose join is exactly `x`, both `f` and `μ(⊥, ·)` satisfy
`∑_{x ≤ y} f x = [y = ⊥]`, so they agree by induction on `y`.
-/

open Finset

namespace Lovasz15

section Crosscut

variable {V : Type*} [CompleteLattice V] [Fintype V] [DecidableEq V]
  [DecidableRel ((· ≤ ·) : V → V → Prop)]
  {AtomsV : Type*} [Fintype AtomsV] [DecidableEq AtomsV]

/-- `atomSignedCount incl x` is the alternating count `∑_S (-1)^|S|` over the sets `S` of atoms
whose join is exactly `x`. -/
def atomSignedCount (incl : AtomsV → V) (x : V) : ℤ :=
  ∑ S ∈ univ.filter (fun S : Finset AtomsV => S.sup incl = x), (-1 : ℤ) ^ S.card

variable (incl : AtomsV → V)

/-- Summing `atomSignedCount` over all `x ≤ y` counts (with signs) all sets of atoms lying
below `y`; this vanishes unless `y = ⊥`. -/
lemma sum_atomSignedCount_le (hatom : ∀ a : AtomsV, IsAtom (incl a))
    (hsurj : ∀ v : V, IsAtom v → ∃ a, incl a = v) (y : V) :
    ∑ x ∈ univ.filter (fun x : V => x ≤ y), atomSignedCount incl x = if y = ⊥ then 1 else 0 := by
  have hmaps : ∀ S ∈ univ.filter (fun S : Finset AtomsV => S.sup incl ≤ y),
      S.sup incl ∈ univ.filter (fun x : V => x ≤ y) := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS ⊢
    exact hS
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun S : Finset AtomsV => (-1 : ℤ) ^ S.card)
  have hstep : ∀ x ∈ univ.filter (fun x : V => x ≤ y), atomSignedCount incl x
      = ∑ S ∈ (univ.filter (fun S : Finset AtomsV => S.sup incl ≤ y)).filter
          (fun S => S.sup incl = x), (-1 : ℤ) ^ S.card := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    unfold atomSignedCount
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hx, h⟩
    · exact fun h => h.2
  rw [Finset.sum_congr rfl hstep, hfib]
  have hset : univ.filter (fun S : Finset AtomsV => S.sup incl ≤ y)
      = (univ.filter (fun a : AtomsV => incl a ≤ y)).powerset := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powerset, Finset.sup_le_iff,
      Finset.subset_iff]
  rw [hset, Finset.sum_powerset_neg_one_pow_card]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h
    by_contra hy
    obtain ⟨v, hv, hvy⟩ := (IsAtomic.eq_bot_or_exists_atom_le (α := V) y).resolve_left hy
    obtain ⟨a, rfl⟩ := hsurj v hv
    have : a ∈ univ.filter (fun a : AtomsV => incl a ≤ y) := by
      simp only [mem_filter, mem_univ, true_and]; exact hvy
    rw [h] at this
    exact absurd this (notMem_empty a)
  · intro hy
    subst hy
    ext a
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, le_bot_iff]
    exact (hatom a).1

/-- The Möbius function satisfies `∑_{x ≤ y} μ(⊥, x) = [y = ⊥]`. -/
lemma sum_mu_le (μ : V → V → ℤ) (μ_self : ∀ a : V, μ a a = 1)
    (μ_rec : ∀ a b : V, a ≠ b →
      μ a b = - ∑ x ∈ univ.filter (fun x : V => a ≤ x ∧ x ≤ b ∧ x ≠ b), μ a x)
    (y : V) :
    ∑ x ∈ univ.filter (fun x : V => x ≤ y), μ ⊥ x = if y = ⊥ then 1 else 0 := by
  by_cases hy : y = ⊥
  · subst hy
    have h : univ.filter (fun x : V => x ≤ ⊥) = {⊥} := by
      ext x; simp [le_bot_iff]
    rw [h, Finset.sum_singleton, μ_self]
    simp
  · simp only [if_neg hy]
    have h : univ.filter (fun x : V => x ≤ y)
        = insert y (univ.filter (fun x : V => ⊥ ≤ x ∧ x ≤ y ∧ x ≠ y)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, bot_le]
      constructor
      · intro hx
        by_cases hxy : x = y
        · exact Or.inl hxy
        · exact Or.inr ⟨hx, hxy⟩
      · rintro (rfl | ⟨hx, -⟩)
        · exact le_rfl
        · exact hx
    rw [h, Finset.sum_insert (by simp), μ_rec ⊥ y (Ne.symm hy)]
    ring

/-- The key identity: the alternating count of the sets of atoms with join `y`
equals `μ(⊥, y)`. -/
lemma atomSignedCount_eq_mu (hatom : ∀ a : AtomsV, IsAtom (incl a))
    (hsurj : ∀ v : V, IsAtom v → ∃ a, incl a = v)
    (μ : V → V → ℤ) (μ_self : ∀ a : V, μ a a = 1)
    (μ_rec : ∀ a b : V, a ≠ b →
      μ a b = - ∑ x ∈ univ.filter (fun x : V => a ≤ x ∧ x ≤ b ∧ x ≠ b), μ a x)
    (y : V) : atomSignedCount incl y = μ ⊥ y := by
  induction y using WellFoundedLT.induction with
  | _ y ih =>
    have h1 := sum_atomSignedCount_le incl hatom hsurj y
    have h2 := sum_mu_le μ μ_self μ_rec y
    have hsplit : univ.filter (fun x : V => x ≤ y)
        = insert y (univ.filter (fun x : V => x ≤ y ∧ x ≠ y)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hx
        by_cases hxy : x = y
        · exact Or.inl hxy
        · exact Or.inr ⟨hx, hxy⟩
      · rintro (rfl | ⟨hx, -⟩)
        · exact le_rfl
        · exact hx
    have hnot : y ∉ univ.filter (fun x : V => x ≤ y ∧ x ≠ y) := by
      simp
    rw [hsplit, Finset.sum_insert hnot] at h1 h2
    have h3 : ∑ x ∈ univ.filter (fun x : V => x ≤ y ∧ x ≠ y), atomSignedCount incl x
        = ∑ x ∈ univ.filter (fun x : V => x ≤ y ∧ x ≠ y), μ ⊥ x := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simp only [mem_filter, mem_univ, true_and] at hx
      exact ih x (lt_of_le_of_ne hx.1 hx.2)
    rw [h3] at h1
    linarith [h1, h2]

end Crosscut

/-- **Crosscut theorem (Lovász, Problem 15).**

Let `V` be a finite lattice with Möbius function `μ` (characterized by `μ a a = 1` and the
recursion `μ a b = - ∑_{a ≤ x < b} μ a x`), and let `AtomsV` be (a copy of) its set of atoms,
of cardinality `n`. If `q l` denotes the number of `l`-element sets of atoms whose join
is `⊤`, then `μ(⊥, ⊤) = ∑_{l = 0}^{n} (-1)^l q l`. -/
theorem Lovasz_15
    (V : Type*)
    [CompleteLattice V] [Fintype V] [DecidableEq V]
    [DecidableRel ((· ≤ ·) : V → V → Prop)]
    (μ : V → V → ℤ)
    (μ_self : ∀ a : V, μ a a = 1)
    (μ_rec :
      ∀ a b : V, a ≠ b →
        μ a b
          = - ∑ x ∈ (Finset.univ.filter (fun x : V => a ≤ x ∧ x ≤ b ∧ x ≠ b)),
              μ a x)
    (n : ℕ) (AtomsV : Type*)
    (incl : AtomsV → V) (isAtom : ∀ a : AtomsV, IsAtom (incl a))
    (isAtom_surjective : ∀ v : V, IsAtom v → ∃ a, incl a = v)
    (eAtoms : AtomsV ≃ Fin n)
    (q : ℕ → ℕ)
    (hq : ∀ k,
      Nonempty
        ({ S : Finset AtomsV // S.card = k ∧ (⨆ i ∈ S, incl i) = (⊤ : V) } ≃ Fin (q k))) :
    μ (⊥ : V) (⊤ : V)
      = ∑ l ∈ Finset.range (n + 1), ((-1 : ℤ) ^ l) * (q l : ℤ) := by
  classical
  let _inst : Fintype AtomsV := Fintype.ofEquiv (Fin n) eAtoms.symm
  have hcard : Fintype.card AtomsV = n := by
    rw [Fintype.card_congr eAtoms, Fintype.card_fin]
  -- reduce to the alternating count
  rw [← atomSignedCount_eq_mu incl isAtom isAtom_surjective μ μ_self μ_rec ⊤]
  -- identify `q l` with the number of `l`-element sets of atoms with join `⊤`
  have hqcard : ∀ l, (q l : ℕ)
      = (univ.filter (fun S : Finset AtomsV => S.card = l ∧ S.sup incl = ⊤)).card := by
    intro l
    obtain ⟨e⟩ := hq l
    have : Fintype.card { S : Finset AtomsV // S.card = l ∧ (⨆ i ∈ S, incl i) = (⊤ : V) }
        = q l := by
      rw [Fintype.card_congr e, Fintype.card_fin]
    rw [← this, Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro S _
    simp [Finset.sup_eq_iSup]
  -- group the sets of atoms by their cardinality
  have hmaps : ∀ S ∈ univ.filter (fun S : Finset AtomsV => S.sup incl = ⊤),
      S.card ∈ Finset.range (n + 1) := by
    intro S _
    simp only [Finset.mem_range, Nat.lt_succ_iff, ← hcard]
    exact Finset.card_le_univ S
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun S : Finset AtomsV => (-1 : ℤ) ^ S.card)
  rw [atomSignedCount, ← hfib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hset : (univ.filter (fun S : Finset AtomsV => S.sup incl = ⊤)).filter
      (fun S => S.card = l)
      = univ.filter (fun S : Finset AtomsV => S.card = l ∧ S.sup incl = ⊤) := by
    ext S
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [hset, hqcard l]
  rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ) ^ l) (fun S hS => by
    simp only [mem_filter] at hS; rw [hS.2.1])]
  simp [mul_comm]

/-- The statement of the problem in its original "tuple" form, as a `Prop`. -/
def TupleFormulation : Prop :=
  ∀ (V : Type) [CompleteLattice V] [Fintype V] [DecidableEq V]
    [DecidableRel ((· ≤ ·) : V → V → Prop)]
    (μ : V → V → ℤ),
    (∀ a : V, μ a a = 1) →
    (∀ a b : V, a ≠ b →
      μ a b = - ∑ x ∈ univ.filter (fun x : V => a ≤ x ∧ x ≤ b ∧ x ≠ b), μ a x) →
    ∀ (n : ℕ) (AtomsV : Type) (incl : AtomsV → V), (∀ a : AtomsV, IsAtom (incl a)) →
    ∀ (_ : AtomsV ≃ Fin n) (q : ℕ → ℕ),
      (∀ k, Nonempty ({ x : (Fin k → AtomsV) // (⨆ i, incl (x i)) = (⊤ : V) } ≃ Fin (q k))) →
      (Fintype.card V ≠ 1 → q 0 = 0) →
      μ (⊥ : V) (⊤ : V) = ∑ l ∈ Finset.range (n + 1), ((-1 : ℤ) ^ l) * (q l : ℤ)

section Counterexamples

/-- The Möbius function of the two element chain `Fin 2`. -/
noncomputable def mu2 : Fin 2 → Fin 2 → ℤ :=
  fun a b => if a = b then 1 else if a < b then -1 else 0

/-- The original statement fails already because `incl` need not enumerate all atoms. -/
theorem not_TupleFormulation_of_partial_atoms : ¬ TupleFormulation := by
  intro h
  have key := h (Fin 2) mu2 (by decide) (by decide) 0 Empty Empty.elim (fun a => a.elim)
    (Equiv.equivOfIsEmpty _ _) (fun _ => 0) ?_ (by decide)
  · revert key
    decide
  · intro k
    have : IsEmpty { x : (Fin k → Empty) // (⨆ i, Empty.elim (x i)) = (⊤ : Fin 2) } := by
      constructor
      rintro ⟨x, hx⟩
      match k with
      | 0 => rw [iSup_of_empty] at hx; exact absurd hx (by decide)
      | (_ + 1) => exact (x 0).elim
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

/-- The four element Boolean lattice. -/
abbrev V4 := Fin 2 × Fin 2

/-- The Möbius function of the four element Boolean lattice. -/
noncomputable def mu4 : V4 → V4 → ℤ := fun a b =>
  if a ≤ b then (-1 : ℤ) ^ ((if a.1 = b.1 then 0 else 1) + (if a.2 = b.2 then 0 else 1)) else 0

/-- The two atoms of the four element Boolean lattice. -/
def incl4 : Bool → V4 := fun b => if b then (0, 1) else (1, 0)

noncomputable instance : DecidableRel ((· < ·) : V4 → V4 → Prop) :=
  fun a b => decidable_of_iff _ (lt_iff_le_not_ge (a := a) (b := b)).symm

lemma isAtom_incl4 (a : Bool) : IsAtom (incl4 a) :=
  ⟨by cases a <;> decide, by cases a <;> decide⟩

lemma iSup_incl4_eq_top_iff {k : ℕ} (x : Fin k → Bool) :
    (⨆ i, incl4 (x i)) = (⊤ : V4) ↔ (∃ i, x i = true) ∧ (∃ i, x i = false) := by
  constructor
  · intro h
    constructor
    · by_contra hc
      push Not at hc
      simp only [Bool.not_eq_true] at hc
      have hle : (⨆ i, incl4 (x i)) ≤ ((1, 0) : V4) := iSup_le (fun i => by rw [hc i]; decide)
      rw [h] at hle
      exact absurd hle (by decide)
    · by_contra hc
      push Not at hc
      simp only [Bool.not_eq_false] at hc
      have hle : (⨆ i, incl4 (x i)) ≤ ((0, 1) : V4) := iSup_le (fun i => by rw [hc i]; decide)
      rw [h] at hle
      exact absurd hle (by decide)
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine top_le_iff.mp ?_
    calc (⊤ : V4) = incl4 (x i) ⊔ incl4 (x j) := by rw [hi, hj]; decide
      _ ≤ (⨆ i, incl4 (x i)) :=
        sup_le (le_iSup (fun i => incl4 (x i)) i) (le_iSup (fun i => incl4 (x i)) j)

lemma card_surjective_tuples (k : ℕ) :
    (univ.filter (fun x : Fin k → Bool => (∃ i, x i = true) ∧ (∃ i, x i = false))).card
      = 2 ^ k - 2 := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hemp : univ.filter (fun x : Fin 0 → Bool => (∃ i, x i = true) ∧ (∃ i, x i = false))
        = ∅ := by
      ext x
      simp
    rw [hemp]
    simp
  · have hcompl : univ.filter (fun x : Fin k → Bool => ¬ ((∃ i, x i = true) ∧ (∃ i, x i = false)))
        = {(fun _ => true), (fun _ => false)} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, not_and_or]
      constructor
      · rintro (h | h)
        · push Not at h
          simp only [Bool.not_eq_true] at h
          exact Or.inr (funext h)
        · push Not at h
          simp only [Bool.not_eq_false] at h
          exact Or.inl (funext h)
      · rintro (rfl | rfl)
        · right; push Not; intro i; decide
        · left; push Not; intro i; decide
    have hne : ((fun _ => true : Fin k → Bool)) ≠ (fun _ => false) := by
      intro hcon
      have := congrFun hcon ⟨0, hk⟩
      simp at this
    have htot := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin k → Bool)))
      (p := fun x : Fin k → Bool => (∃ i, x i = true) ∧ (∃ i, x i = false))
    rw [hcompl, Finset.card_pair hne] at htot
    have huniv : (univ : Finset (Fin k → Bool)).card = 2 ^ k := by
      simp [Finset.card_univ]
    omega

/-- The original "tuple" statement is false: in the four element Boolean lattice
`μ ⊥ ⊤ = 1`, while the alternating sum of the numbers of tuples of atoms equals `2`. -/
theorem not_TupleFormulation : ¬ TupleFormulation := by
  intro h
  have key := h V4 mu4 (by decide) (by decide) 2 Bool incl4 isAtom_incl4
    finTwoEquiv.symm (fun k => 2 ^ k - 2) ?_ (by decide)
  · norm_num [Finset.sum_range_succ] at key
    revert key
    decide
  · intro k
    classical
    refine ⟨Fintype.equivFinOfCardEq ?_⟩
    rw [Fintype.card_subtype]
    rw [Finset.filter_congr (q := fun x : Fin k → Bool => (∃ i, x i = true) ∧ (∃ i, x i = false))
      (fun x _ => by simp [iSup_incl4_eq_top_iff x])]
    exact card_surjective_tuples k

/-!
## A sanity check for `Lovasz_15`
-/

theorem surj_incl4 : ∀ v : V4, IsAtom v → ∃ a, incl4 a = v := by
  rintro ⟨v1, v2⟩ hv
  fin_cases v1 <;> fin_cases v2
  · exact absurd rfl hv.1
  · exact ⟨true, by decide⟩
  · exact ⟨false, by decide⟩
  · exact absurd (hv.2 (0, 1) (by decide)) (by decide)

theorem card_atom_subsets (k : ℕ) :
    (univ.filter (fun S : Finset Bool => S.card = k ∧ S.sup incl4 = ⊤)).card
      = (if k = 2 then 1 else 0) := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (n + 3) =>
    have hemp : univ.filter (fun S : Finset Bool => S.card = n + 3 ∧ S.sup incl4 = ⊤) = ∅ := by
      ext S
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
      intro _
      have hle := Finset.card_le_univ S
      simp [Fintype.card_bool] at hle
      omega
    simp [hemp]

example : mu4 ⊥ ⊤ = 1 := by
  have key := Lovasz_15 V4 mu4 (by decide) (by decide) 2 Bool incl4 isAtom_incl4 surj_incl4
      finTwoEquiv.symm (fun k => if k = 2 then 1 else 0) (by
        intro k
        classical
        refine ⟨Fintype.equivFinOfCardEq ?_⟩
        rw [Fintype.card_subtype]
        rw [Finset.filter_congr (q := fun S : Finset Bool => S.card = k ∧ S.sup incl4 = ⊤)
          (fun S _ => by simp [Finset.sup_eq_iSup])]
        exact card_atom_subsets k)
  rw [key]
  decide

end Counterexamples

end Lovasz15
