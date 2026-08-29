import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-! # Parking functions: `H(5) = 1296`

`n` cars arrive in order at `n` parking spots along a one-way street. Car `c` has a
favourite spot `f c` and parks at the first free spot at or after `f c`; if there is
none, the process is unsuccessful. We count the preference functions
`f : Fin n → Fin n` for which every car parks (these are exactly the *parking
functions* of length `n`), and show that for `n = 5` there are `1296 = 6^4` of them.
-/

/-- A preference function: each of the `n` cars picks a favourite spot.
Defined as `abbrev` so typeclass instances for `Fin n → Fin n` are inherited transparently. -/
abbrev ParkingPref (n : ℕ) := Fin n → Fin n

/-- The classical characterisation of a successful process: for every spot `m`,
at least `m + 1` cars have a favourite spot among `0, …, m`. -/
def ParkingSuccess {n : ℕ} (f : ParkingPref n) : Prop :=
  ∀ m : Fin n,
    (Finset.filter (fun c : Fin n => (f c).val ≤ m.val) Finset.univ).card ≥ m.val.succ

instance instDecidableParkingSuccess {n : ℕ} (f : ParkingPref n) :
    Decidable (ParkingSuccess f) := by
  unfold ParkingSuccess
  infer_instance

/-- The successful preference functions. -/
def SuccessfulPrefs (n : ℕ) : Type :=
  { f : ParkingPref n // ParkingSuccess f }

instance instFintypeSuccessfulPrefs (n : ℕ) : Fintype (SuccessfulPrefs n) :=
  inferInstanceAs (Fintype { f : ParkingPref n // ParkingSuccess f })

/-- `H n`, the number of successful parking processes with `n` spots. -/
def H (n : ℕ) : ℕ := Fintype.card (SuccessfulPrefs n)

/-- There are exactly `1296` successful preference functions for `n = 5`. -/
theorem card_SuccessfulPrefs_five : Fintype.card (SuccessfulPrefs 5) = 1296 := by
  decide

theorem H_five : H 5 = 1296 := card_SuccessfulPrefs_five

/-- `H(5) = 1296`, stated as a bijection with `Fin 1296`. -/
theorem bona_9 :
  Nonempty (SuccessfulPrefs 5 ≃ Fin 1296) :=
  ⟨Fintype.equivFinOfCardEq card_SuccessfulPrefs_five⟩

/-! ## The literal parking process -/

/-- The first free spot at or after `s`, if any. -/
def findSpot (n : ℕ) (occ : List ℕ) (s : ℕ) : Option ℕ :=
  (List.range n).find? (fun j => decide (s ≤ j) && !(occ.contains j))

/-- Run the cars, in order, through the parking process; the result is the list of
occupied spots, or `none` if some car failed to park. -/
def parkFold (n : ℕ) (prefs : List ℕ) : Option (List ℕ) :=
  prefs.foldl (fun acc s => acc.bind (fun occ => (findSpot n occ s).map (fun j => j :: occ)))
    (some [])

/-- The parking process for preference function `f` is successful. -/
def ProcessSuccess {n : ℕ} (f : ParkingPref n) : Prop :=
  (parkFold n ((List.ofFn f).map Fin.val)).isSome

instance instDecidableProcessSuccess {n : ℕ} (f : ParkingPref n) :
    Decidable (ProcessSuccess f) := by
  unfold ProcessSuccess; infer_instance

/-- For `n = 5`, the parking process succeeds exactly for the preference functions
satisfying the counting condition `ParkingSuccess`. -/
theorem processSuccess_iff_parkingSuccess_five (f : ParkingPref 5) :
    ProcessSuccess f ↔ ParkingSuccess f := by
  revert f
  decide

/-- The number of preference functions for which the parking process succeeds is
`1296` when `n = 5`. -/
theorem card_processSuccess_five :
    Fintype.card { f : ParkingPref 5 // ProcessSuccess f } = 1296 := by
  decide

/-- `H(5) = 1296` for the literal parking process, stated as a bijection with `Fin 1296`. -/
theorem processSuccess_five_equiv_fin :
    Nonempty ({ f : ParkingPref 5 // ProcessSuccess f } ≃ Fin 1296) :=
  ⟨Fintype.equivFinOfCardEq card_processSuccess_five⟩
