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
# Unique normal subgroup of index `q`

If `|G| = q * p ^ n` with `p > q` primes, then `G` contains a unique normal subgroup
of index `q`, equivalently a unique normal subgroup of order `p ^ n`.

The tool used is **Sylow's theorem** (option (d) of the multiple-choice question):
a Sylow `p`-subgroup `P` has order `p ^ n` and index `q`; the number `n_p` of Sylow
`p`-subgroups divides `q` and satisfies `n_p ≡ 1 [MOD p]`.  Since `q < p`, the value
`n_p = q` is impossible, so `n_p = 1`, i.e. `P` is the unique Sylow `p`-subgroup and
is therefore normal.  Any subgroup of order `p ^ n` is a Sylow `p`-subgroup, hence
equals `P`.
-/

theorem Q21
    (G : Type*) [Group G] [Fintype G]
    (p q n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hq_lt_hp : q < p)
    (hcard : Fintype.card G = q * p ^ n) :
    ∃! H : Subgroup G, Subgroup.Normal H ∧ Nonempty (↥H ≃ Fin (p ^ n)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hpq : ¬ p ∣ q := fun hd => absurd (Nat.le_of_dvd hq.pos hd) (by omega)
  have hG : Nat.card G = q * p ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hfac : (Nat.card G).factorization p = n := by
    rw [hG, Nat.factorization_mul hq.ne_zero (pow_ne_zero n hp.ne_zero)]
    simp [Nat.factorization_eq_zero_of_not_dvd hpq, hp.factorization_pow]
  -- There is exactly one Sylow `p`-subgroup.
  have hsub : Subsingleton (Sylow p G) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    have hPc : Nat.card ((P : Subgroup G)) = p ^ n := by rw [P.card_eq_multiplicity, hfac]
    have hidx : (P : Subgroup G).index = q := by
      have h := Subgroup.card_mul_index (P : Subgroup G)
      rw [hPc, hG] at h
      have hpn : 0 < p ^ n := pow_pos hp.pos n
      exact Nat.eq_of_mul_eq_mul_left hpn (by linarith [h])
    have hdvd : Nat.card (Sylow p G) ∣ q := by rw [← hidx]; exact P.card_dvd_index
    have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    have h1 : Nat.card (Sylow p G) = 1 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h | h
      · exact h
      · exfalso
        rw [h] at hmod
        have h2 : q % p = 1 % p := hmod
        rw [Nat.mod_eq_of_lt hq_lt_hp, Nat.mod_eq_of_lt hp1] at h2
        omega
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hPcard : Nat.card ((P : Subgroup G)) = p ^ n := by rw [P.card_eq_multiplicity, hfac]
  refine ⟨(P : Subgroup G), ⟨P.normal_of_subsingleton, ⟨Finite.equivFinOfCardEq hPcard⟩⟩, ?_⟩
  rintro H ⟨-, ⟨e⟩⟩
  have hHcard : Nat.card H = p ^ (Nat.card G).factorization p := by
    rw [hfac]; exact Nat.card_eq_of_equiv_fin e
  have hPeq : Sylow.ofCard H hHcard = P := Subsingleton.elim _ _
  calc H = ((Sylow.ofCard H hHcard : Sylow p G) : Subgroup G) := (Sylow.coe_ofCard H hHcard).symm
    _ = (P : Subgroup G) := by rw [hPeq]
