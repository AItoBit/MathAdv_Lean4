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
# Hotel assignments (Bóna, combinatorial 4.9)

`n` tourists arrive on `n` consecutive days; the tourist arriving on day `i` may choose any
hotel from `1, …, i`.  `H (n, k)` is the number of choice functions for which exactly `k`
hotels are used.

The choices are modelled as functions `f : Fin n → Fin n` with `f i ≤ i` (0-indexed: the
tourist of day `i` picks a hotel among `0, …, i`), and `usedHotels f` is the number of hotels
actually used.
-/

/-- An assignment of a hotel to each of the `n` tourists. -/
def HotelAssign (n : ℕ) := Fin n → Fin n

/-- The tourist arriving on day `i` can only afford the hotels `0, …, i`. -/
def AdmissibleChoice {n : ℕ} (f : HotelAssign n) : Prop :=
  ∀ i : Fin n, f i ≤ i

/-- The number of hotels that host at least one tourist. -/
def usedHotels {n : ℕ} (f : HotelAssign n) : ℕ :=
  (Finset.univ.image f).card

/-- The admissible assignments using exactly `k` hotels. -/
def ValidHotelAssignments (n k : ℕ) : Type :=
  { f : HotelAssign n // AdmissibleChoice f ∧ usedHotels f = k }

instance instFintypeHotelAssign (n : ℕ) : Fintype (HotelAssign n) :=
  inferInstanceAs (Fintype (Fin n → Fin n))

instance instDecidableEqHotelAssign (n : ℕ) : DecidableEq (HotelAssign n) :=
  inferInstanceAs (DecidableEq (Fin n → Fin n))

instance instDecidableAdmissibleChoice {n : ℕ} (f : HotelAssign n) :
    Decidable (AdmissibleChoice f) :=
  inferInstanceAs (Decidable (∀ i : Fin n, f i ≤ i))

instance instFintypeValidHotelAssignments (n k : ℕ) : Fintype (ValidHotelAssignments n k) :=
  inferInstanceAs (Fintype { f : HotelAssign n // AdmissibleChoice f ∧ usedHotels f = k })

/-- Reading a "day `i` picks one of the `i+1` cheapest hotels" choice as a hotel assignment. -/
def liftFin {n : ℕ} (g : ∀ i : Fin n, Fin ((i : ℕ) + 1)) : HotelAssign n :=
  fun i => ⟨(g i : ℕ), by have h1 := (g i).isLt; have h2 := i.isLt; omega⟩

/-- The same objects as `ValidHotelAssignments n k`, but encoded on the (much smaller,
`n!`-element) dependent product type. -/
def PiBelow (n k : ℕ) : Type :=
  { g : (∀ i : Fin n, Fin ((i : ℕ) + 1)) // (Finset.univ.image (liftFin g)).card = k }

instance instFintypePiBelow (n k : ℕ) : Fintype (PiBelow n k) :=
  inferInstanceAs (Fintype { g : (∀ i : Fin n, Fin ((i : ℕ) + 1)) //
    (Finset.univ.image (liftFin g)).card = k })

theorem AdmissibleChoice.lt_succ {n : ℕ} {f : HotelAssign n} (hf : AdmissibleChoice f)
    (i : Fin n) : ((f i : Fin n) : ℕ) < (i : ℕ) + 1 :=
  Nat.lt_succ_of_le (Fin.le_def.mp (hf i))

theorem liftFin_lower {n : ℕ} {f : HotelAssign n} (hf : AdmissibleChoice f) :
    liftFin (fun i => (⟨((f i : Fin n) : ℕ), hf.lt_succ i⟩ : Fin ((i : ℕ) + 1))) = f := by
  funext i; apply Fin.ext; rfl

/-- The two encodings of the admissible assignments agree. -/
def validEquivPiBelow (n k : ℕ) : ValidHotelAssignments n k ≃ PiBelow n k where
  toFun f :=
    ⟨fun i => ⟨((f.1 i : Fin n) : ℕ), f.2.1.lt_succ i⟩, by
      rw [liftFin_lower f.2.1]; exact f.2.2⟩
  invFun g :=
    ⟨liftFin g.1, fun i => Fin.le_def.mpr (Nat.lt_succ_iff.mp (g.1 i).isLt), g.2⟩
  left_inv f := by apply Subtype.ext; funext i; apply Fin.ext; rfl
  right_inv g := by apply Subtype.ext; funext i; apply Fin.ext; rfl

theorem card_ValidHotelAssignments (n k : ℕ) :
    Fintype.card (ValidHotelAssignments n k) =
      ((Finset.univ : Finset (∀ i : Fin n, Fin ((i : ℕ) + 1))).filter
        (fun g => (Finset.univ.image (liftFin g)).card = k)).card := by
  rw [Fintype.card_congr (validEquivPiBelow n k)]
  exact Fintype.card_subtype _

set_option maxRecDepth 100000 in
/-- Exactly `1191` of the `7!` admissible assignments of 7 tourists use exactly 3 hotels. -/
theorem card_valid_7_3 : Fintype.card (ValidHotelAssignments 7 3) = 1191 := by
  rw [card_ValidHotelAssignments]
  decide

set_option maxRecDepth 100000 in
/-- Exactly `2416` of the `7!` admissible assignments of 7 tourists use exactly 4 hotels. -/
theorem card_valid_7_4 : Fintype.card (ValidHotelAssignments 7 4) = 2416 := by
  rw [card_ValidHotelAssignments]
  decide

/-- `H n k` is the number of admissible assignments of `n` tourists using exactly `k` hotels. -/
def H (n k : ℕ) : ℕ := Fintype.card (ValidHotelAssignments n k)

/-- With `k` counting the hotels that host at least one tourist, `H 7 4 = 2416`
(the value `2416` claimed in the problem for `H(7,3)`; see `not_bona_7_original` below,
the discrepancy is an index shift in the definition of `H`). -/
theorem H_7_4 : H 7 4 = 2416 := card_valid_7_4

/-- With `k` counting the hotels that host at least one tourist, `H 7 3 = 1191`. -/
theorem H_7_3 : H 7 3 = 1191 := card_valid_7_3

/-!
The statement as originally posed,

```
theorem bona_7 : Nonempty (ValidHotelAssignments 7 3 ≃ Fin 2416)
```

is **false**: exactly `1191` admissible assignments of `7` tourists use exactly `3` hotels,
while `2416` is the number of admissible assignments using exactly `4` hotels.  (The counts
for `k = 1, …, 7` are `1, 120, 1191, 2416, 1191, 120, 1`, the Eulerian numbers of order `7`;
the claimed identity `H(7,3) = 2416` therefore corresponds to a shifted indexing convention.)
Both the refutation and the corrected statements are given below.
-/

/-- The originally posed statement is false. -/
theorem not_bona_7_original : ¬ Nonempty (ValidHotelAssignments 7 3 ≃ Fin 2416) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  rw [card_valid_7_3, Fintype.card_fin] at h
  omega

/-- Corrected version of `bona_7`: there are exactly `2416` admissible assignments of
`7` tourists that use exactly `4` hotels. -/
theorem bona_7_corrected : Nonempty (ValidHotelAssignments 7 4 ≃ Fin 2416) :=
  ⟨Fintype.equivFinOfCardEq card_valid_7_4⟩

/-- The count for exactly `3` hotels: there are `1191` such assignments. -/
theorem bona_7_three_hotels : Nonempty (ValidHotelAssignments 7 3 ≃ Fin 1191) :=
  ⟨Fintype.equivFinOfCardEq card_valid_7_3⟩
