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

/-! ## Q20: Noetherian rings are exactly those with all ideals finitely generated -/

/-- A commutative ring `R` satisfies the ascending chain condition on ideals
(i.e. is Noetherian) if and only if every ideal of `R` is finitely generated.
(The integral-domain hypothesis of the original statement is not needed.) -/
theorem Q20
    (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff_ideal_fg R

/-! ## Q21: a group of order `q * p ^ n` with `q < p` primes -/

/-- If `q < p` are primes, the multiplicity of `p` in `q * p ^ n` is `n`. -/
lemma factorization_q_mul_pow (p q n : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hqp : q < p) : (q * p ^ n).factorization p = n := by
  have hpq : ¬ p ∣ q := fun h => absurd (Nat.le_of_dvd hq.pos h) (by omega)
  rw [Nat.factorization_mul hq.ne_zero (pow_ne_zero n hp.ne_zero)]
  simp [Nat.factorization_eq_zero_of_not_dvd hpq, Nat.Prime.factorization_pow hp]

/-- Under the hypotheses of Q21 there is exactly one Sylow `p`-subgroup. -/
lemma card_sylow_eq_one_of_lt (G : Type*) [Group G] [Finite G] (p q n : ℕ)
    [hp : Fact p.Prime] (hq : Nat.Prime q) (hqp : q < p)
    (hcard : Nat.card G = q * p ^ n) :
    Nat.card (Sylow p G) = 1 := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hPcard : Nat.card P = p ^ n := by
    rw [P.card_eq_multiplicity, hcard, factorization_q_mul_pow p q n hp.out hq hqp]
  have hindex : (P : Subgroup G).index = q := by
    have := Subgroup.card_mul_index (P : Subgroup G)
    rw [hPcard, hcard] at this
    have hppos : 0 < p ^ n := pow_pos hp.out.pos n
    have : p ^ n * (P : Subgroup G).index = p ^ n * q := by linarith [this, Nat.mul_comm q (p ^ n)]
    exact Nat.eq_of_mul_eq_mul_left hppos this
  have hdvd : Nat.card (Sylow p G) ∣ q := hindex ▸ P.card_dvd_index
  have hle : Nat.card (Sylow p G) ≤ q := Nat.le_of_dvd hq.pos hdvd
  have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hpos : 0 < Nat.card (Sylow p G) := Nat.card_pos
  have := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  have hlt : Nat.card (Sylow p G) - 1 < p := by omega
  have : Nat.card (Sylow p G) - 1 = 0 := by
    rcases Nat.eq_zero_or_pos (Nat.card (Sylow p G) - 1) with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd h this) (by omega)
  omega

/-- **Q21.** If `|G| = q * p ^ n` with `q < p` primes, then `G` has a unique normal
subgroup of order `p ^ n` (equivalently, of index `q`): the unique Sylow `p`-subgroup. -/
theorem Q21
    (G : Type*) [Group G] [Fintype G]
    (p q n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hq_lt_hp : q < p)
    (hcard : Fintype.card G = q * p ^ n) :
    ∃! H : Subgroup G, Subgroup.Normal H ∧ Nonempty (↥H ≃ Fin (p ^ n)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard' : Nat.card G = q * p ^ n := by rwa [Nat.card_eq_fintype_card]
  have hfac : (Nat.card G).factorization p = n := by
    rw [hcard', factorization_q_mul_pow p q n hp hq hq_lt_hp]
  haveI : Subsingleton (Sylow p G) := by
    have h1 : Nat.card (Sylow p G) = 1 := card_sylow_eq_one_of_lt G p q n hq hq_lt_hp hcard'
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hPcard : Nat.card (P : Subgroup G) = p ^ n := by rw [P.card_eq_multiplicity, hfac]
  refine ⟨(P : Subgroup G), ⟨Sylow.normal_of_subsingleton P, ⟨?_⟩⟩, ?_⟩
  · have : Fintype.card (P : Subgroup G) = p ^ n := by
      rwa [← Nat.card_eq_fintype_card]
    exact Fintype.equivFinOfCardEq this
  · rintro H ⟨-, ⟨e⟩⟩
    have hH : Nat.card H = p ^ (Nat.card G).factorization p := by
      rw [hfac, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    have : Sylow.ofCard H hH = P := Subsingleton.elim _ _
    calc H = ↑(Sylow.ofCard H hH) := (Sylow.coe_ofCard H hH).symm
      _ = (P : Subgroup G) := by rw [this]
