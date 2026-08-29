import Mathlib

/-!
# Non-attacking rook placements on an `n × n` board

The number of ways to place `n` rooks on an `n × n` chessboard so that no two attack
each other (i.e. no two share a row or a column) is `n !`.

We give two formalizations:

* `bona_1`: the number of bijections `Fin n → Fin n` is `n !`;
* `card_rookPlacements`: the number of `n`-element sets of squares of the board with
  pairwise distinct rows and pairwise distinct columns is `n !`.
-/

open Finset

/-- The number of bijections of an `n`-element set to itself is `n !`. -/
theorem bona_1 (n : ℕ) :
    Fintype.card { f : Fin n → Fin n // Function.Bijective f } = Nat.factorial n := by
  have e : { f : Fin n → Fin n // Function.Bijective f } ≃ Equiv.Perm (Fin n) :=
    { toFun := fun f => Equiv.ofBijective f.1 f.2
      invFun := fun e => ⟨e, e.bijective⟩
      left_inv := fun f => rfl
      right_inv := fun e => Equiv.ext fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]

/-- A *placement of `n` non-attacking rooks* on the `n × n` board: a set of `n` squares,
no two of which lie in the same row or in the same column. -/
def IsRookPlacement {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  S.card = n ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

instance {n : ℕ} (S : Finset (Fin n × Fin n)) : Decidable (IsRookPlacement S) := by
  unfold IsRookPlacement; infer_instance

/-- The finite set of all placements of `n` non-attacking rooks on the `n × n` board. -/
def rookPlacements (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  Finset.univ.filter IsRookPlacement

/-- The set of squares occupied by the rooks associated with a permutation `σ`. -/
def permRookSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun i => (i, σ i)

lemma mem_permRookSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ permRookSet σ ↔ σ p.1 = p.2 := by
  constructor
  · rintro h
    simp only [permRookSet, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, hi⟩ := h
    cases hi; rfl
  · intro h
    simp only [permRookSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨p.1, by rw [h]⟩

lemma permRookSet_isRookPlacement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsRookPlacement (permRookSet σ) := by
  constructor
  · rw [permRookSet, Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq .. ▸ hab).1),
      Finset.card_univ, Fintype.card_fin]
  · intro p hp q hq hpq
    rw [mem_permRookSet] at hp hq
    constructor
    · rintro h
      exact hpq (Prod.ext h (by rw [← hp, ← hq, h]))
    · rintro h
      have : p.1 = q.1 := by
        apply σ.injective
        rw [hp, hq, h]
      exact hpq (Prod.ext this (by rw [← hp, ← hq, this]))

lemma permRookSet_injective {n : ℕ} : Function.Injective (permRookSet (n := n)) := by
  intro σ τ h
  ext i
  have : (i, σ i) ∈ permRookSet τ := by rw [← h, mem_permRookSet]
  rw [mem_permRookSet] at this
  have h2 : τ i = σ i := this
  exact congrArg Fin.val h2.symm

/-- Every non-attacking rook placement comes from a permutation. -/
lemma exists_perm_of_isRookPlacement {n : ℕ} (S : Finset (Fin n × Fin n))
    (hS : IsRookPlacement S) : ∃ σ : Equiv.Perm (Fin n), permRookSet σ = S := by
  obtain ⟨hcard, hpair⟩ := hS
  -- the first projection is injective on `S`
  have hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q := by
    intro p hp q hq h
    by_contra hpq
    exact (hpair p hp q hq hpq).1 h
  have himg : S.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_fin]
  have hex : ∀ i : Fin n, ∃ j : Fin n, (i, j) ∈ S := by
    intro i
    have : i ∈ S.image Prod.fst := by rw [himg]; exact Finset.mem_univ i
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp this
    exact ⟨p.2, by simpa [← hpi] using hp⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have := (hpair (a, f a) (hf a) (b, f b) (hf b) (by simp [hne])).2
    exact this hab
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    rw [mem_permRookSet] at hp
    simp only [Equiv.ofBijective_apply] at hp
    have := hf p.1
    rwa [hp] at this
  · rw [hcard, (permRookSet_isRookPlacement _).1]

/-- The number of ways to place `n` non-attacking rooks on an `n × n` board is `n !`. -/
theorem card_rookPlacements (n : ℕ) : (rookPlacements n).card = Nat.factorial n := by
  have : (rookPlacements n).card = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Fintype.card, ← Finset.card_image_of_injective (Finset.univ) permRookSet_injective]
    congr 1
    ext S
    simp only [rookPlacements, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hS
      obtain ⟨σ, hσ⟩ := exists_perm_of_isRookPlacement S hS
      exact ⟨σ, hσ⟩
    · rintro ⟨σ, hσ⟩
      subst hσ
      exact permRookSet_isRookPlacement σ
  rw [this, Fintype.card_perm, Fintype.card_fin]
