import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
-- (`open scoped Classical` from the original header is omitted: the classical decidability
-- instance it introduces would obstruct the `decide` computations used below.)

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
# Luke Skywalker and the three strangers

Luke questions three strangers `A`, `B`, `C`, whose roles are, in some order, a Sith lord,
a mad Hermit and a Jedi master.

* The Sith knows everybody's identity.  He calls himself the Jedi, he calls the Jedi the Sith,
  and he speaks at random about the Hermit (he calls the Hermit either the Hermit or the Jedi,
  each with probability `1/2`); in particular the Sith never accuses the Hermit of being the Sith,
  since the accusation of being the Sith is reserved for the real Jedi.
* The Jedi knows only his own role.  He answers truthfully when he can, and answers uniformly
  at random when he does not know the answer.
* The Hermit answers uniformly at random.

The conversation is

* Luke: "A, are you the Sith?"   A: "No".
* Luke: "B, is A the Sith?"      B: "Yes".
* Luke: "A, are you the Hermit?" A: "No".
* Luke: "C, are you the Hermit?" C: "No".

We build the (finite, uniform) probability space describing this situation and prove that the
conditional probability that `A` is the Sith, given the four answers, equals `2/5`.

The Bayes computation behind the answer is recorded in `coinCount_values`: given each of the six
possible role assignments, the number of coin tosses (out of `16`) producing the observed answers
is, respectively,

```
(Sith, Hermit, Jedi) : 8      (Sith, Jedi, Hermit) : 4
(Hermit, Sith, Jedi) : 0      (Jedi, Sith, Hermit) : 8
(Hermit, Jedi, Sith) : 2      (Jedi, Hermit, Sith) : 8
```

so that (dividing every likelihood by `16`, and then by `2`, which is the normalisation
`0.5 → 0.25`, `0.25 → 0.125`, ... used in the informal solution) the answer is

`(0.125 + 0.25) / 0.9375 = 2/5`.
-/

namespace Skywalker

open MeasureTheory ENNReal

/-- The three possible roles. -/
inductive Role | Sith | Hermit | Jedi
  deriving DecidableEq, Fintype, Repr

open Role

/-- The role that the Sith lord attributes to a person whose true role is `t`,
using the fair coin `c` when he speaks about the Hermit. -/
def sithClaim : Role → Bool → Role
  | Sith, _ => Jedi      -- he calls himself the Jedi
  | Jedi, _ => Sith      -- he frames the Jedi as the Sith
  | Hermit, c => if c then Hermit else Jedi   -- he speaks at random about the Hermit

/-- `answer responder target query coin` is the yes/no answer given by a person whose role is
`responder`, to the question "is the person whose role is `target` the `query`?", using the fair
coin `coin` for random answers.  (The function is only used with `target = responder` or with
`target ≠ responder`, the roles of the three people being pairwise distinct.) -/
def answer (responder target query : Role) (coin : Bool) : Bool :=
  match responder with
  | Hermit => coin                                    -- always answers at random
  | Sith => decide (sithClaim target coin = query)    -- answers according to his own story
  | Jedi => if target = Jedi then decide (query = Jedi)   -- he knows his own role
            else coin                                     -- otherwise he has no idea

/-- The possible assignments of roles to `A`, `B`, `C`: all three roles are distinct. -/
abbrev Assign := {r : Role × Role × Role // r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2}

/-- The sample space: a role assignment together with the four fair coins used for the four
(possibly random) answers. -/
abbrev Om := Assign × Bool × Bool × Bool × Bool

instance : MeasurableSpace Om := ⊤
instance : MeasurableSingletonClass Om := ⟨fun _ => trivial⟩
instance : Nonempty Om := ⟨⟨⟨(Sith, Hermit, Jedi), by decide⟩, false, false, false, false⟩⟩

/-- The role of `A`. -/
def rA (w : Om) : Role := w.1.1.1
/-- The role of `B`. -/
def rB (w : Om) : Role := w.1.1.2.1
/-- The role of `C`. -/
def rC (w : Om) : Role := w.1.1.2.2

/-- The three roles really are a permutation of `Sith, Hermit, Jedi`. -/
theorem roles_perm (w : Om) :
    ({rA w, rB w, rC w} : Finset Role) = ({Sith, Hermit, Jedi} : Finset Role) := by
  obtain ⟨⟨⟨a, b, c⟩, h⟩, -⟩ := w
  revert h
  simp only [rA, rB, rC]
  revert a b c
  decide

/-- Answer to "A, are you the Sith?". -/
def ans1 (w : Om) : Bool := answer (rA w) (rA w) Sith w.2.1
/-- Answer to "B, is A the Sith?". -/
def ans2 (w : Om) : Bool := answer (rB w) (rA w) Sith w.2.2.1
/-- Answer to "A, are you the Hermit?". -/
def ans3 (w : Om) : Bool := answer (rA w) (rA w) Hermit w.2.2.2.1
/-- Answer to "C, are you the Hermit?". -/
def ans4 (w : Om) : Bool := answer (rC w) (rC w) Hermit w.2.2.2.2

/-- The observed conversation, as a boolean predicate:
"No", "Yes", "No", "No". -/
def evidenceB (w : Om) : Bool :=
  (ans1 w == false) && (ans2 w == true) && (ans3 w == false) && (ans4 w == false)

/-- The event "Luke hears the answers No, Yes, No, No". -/
def Evidence : Set Om := {w | evidenceB w = true}

/-- The event "`A` is the Sith lord". -/
def ASith : Set Om := {w | rA w = Sith}

instance : DecidablePred (· ∈ Evidence) := fun w =>
  inferInstanceAs (Decidable (evidenceB w = true))
instance : DecidablePred (· ∈ ASith) := fun w => inferInstanceAs (Decidable (rA w = Sith))
instance : DecidablePred (· ∈ ASith ∩ Evidence) := fun w =>
  inferInstanceAs (Decidable (w ∈ ASith ∧ w ∈ Evidence))

/-- The uniform probability measure on the sample space: the role assignment is uniform among
the six permutations and the four coins are independent fair coins. -/
noncomputable def mu : Measure Om := (PMF.uniformOfFintype Om).toMeasure

instance : IsProbabilityMeasure mu := by
  unfold mu; infer_instance

/-- For a fixed role assignment, the number of the `16` coin tosses that produce the observed
answers. -/
def coinCount (a : Assign) : ℕ :=
  (Finset.univ.filter (fun c : Bool × Bool × Bool × Bool => evidenceB (a, c) = true)).card

/-- The likelihoods of the observed conversation under the six role assignments
(out of `16` equally likely coin tosses each).  Note the vanishing likelihood of
`(A, B, C) = (Hermit, Sith, Jedi)`: the Sith `B` would never call the Hermit `A` a Sith. -/
theorem coinCount_values :
    coinCount ⟨(Sith, Hermit, Jedi), by decide⟩ = 8 ∧
    coinCount ⟨(Sith, Jedi, Hermit), by decide⟩ = 4 ∧
    coinCount ⟨(Hermit, Sith, Jedi), by decide⟩ = 0 ∧
    coinCount ⟨(Jedi, Sith, Hermit), by decide⟩ = 8 ∧
    coinCount ⟨(Hermit, Jedi, Sith), by decide⟩ = 2 ∧
    coinCount ⟨(Jedi, Hermit, Sith), by decide⟩ = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem card_Om : Fintype.card Om = 96 := by decide

theorem card_Evidence : Fintype.card ↥Evidence = 30 := by decide

theorem card_ASith_inter_Evidence : Fintype.card ↥(ASith ∩ Evidence) = 12 := by decide

/-- The probability of hearing the four observed answers is `30/96 = 5/16`. -/
theorem mu_Evidence : mu Evidence = 5 / 16 := by
  rw [mu, PMF.toMeasure_uniformOfFintype_apply Evidence (by trivial), card_Evidence, card_Om]
  rw [show ((30 : ℕ) : ℝ≥0∞) = 30 by norm_num, show ((96 : ℕ) : ℝ≥0∞) = 96 by norm_num]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_div]
  norm_num

/-- The probability that `A` is the Sith *and* Luke hears the four observed answers
is `12/96 = 1/8`. -/
theorem mu_ASith_inter_Evidence : mu (ASith ∩ Evidence) = 1 / 8 := by
  rw [mu, PMF.toMeasure_uniformOfFintype_apply (ASith ∩ Evidence) (by trivial),
    card_ASith_inter_Evidence, card_Om]
  rw [show ((12 : ℕ) : ℝ≥0∞) = 12 by norm_num, show ((96 : ℕ) : ℝ≥0∞) = 96 by norm_num]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_div]
  norm_num

/-- **The answer.**  Given the conversation "No", "Yes", "No", "No", the probability that `A`
is the Sith lord equals `2/5`. -/
theorem prob_A_is_Sith_given_evidence :
    mu (ASith ∩ Evidence) / mu Evidence = 2 / 5 := by
  rw [mu_ASith_inter_Evidence, mu_Evidence]
  rw [← ENNReal.toReal_eq_toReal_iff' (by
        refine ENNReal.div_ne_top (by finiteness) ?_
        simp [ENNReal.div_eq_zero_iff]) (by finiteness)]
  simp [ENNReal.toReal_div]
  norm_num

/-- The same statement, phrased with Mathlib's conditional probability `μ[·|·]`. -/
theorem cond_prob_A_is_Sith :
    (ProbabilityTheory.cond mu Evidence) ASith = 2 / 5 := by
  rw [ProbabilityTheory.cond_apply (by trivial), Set.inter_comm, ← ENNReal.div_eq_inv_mul,
    prob_A_is_Sith_given_evidence]

/-!
### The literal statement without a behavioural model

Without any hypothesis relating the four answers to the roles of `A`, `B`, `C`, the statement
of the problem is not provable: the four answers may, for instance, be constant, and `A` may be
the Sith with probability one.  The following theorem records this.
-/

/-- Formalised without modelling the behaviour of the three strangers, the claim is false. -/
theorem underdetermined_statement_is_false :
    ¬ ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (A B C : Ω → Role),
        (∀ w, ({A w, B w, C w} : Finset Role) = ({Sith, Hermit, Jedi} : Finset Role)) →
        ∀ a1 a2 a3 a4 : Ω → Bool,
        μ ({w | A w = Sith} ∩
            {w | a1 w = false ∧ a2 w = true ∧ a3 w = false ∧ a4 w = false}) /
          μ {w | a1 w = false ∧ a2 w = true ∧ a3 w = false ∧ a4 w = false} = 2 / 5 := by
  intro h
  have := h Unit ⊤ (Measure.dirac ()) (by infer_instance)
    (fun _ => Sith) (fun _ => Hermit) (fun _ => Jedi) (fun _ => rfl)
    (fun _ => false) (fun _ => true) (fun _ => false) (fun _ => false)
  rw [show ({w : Unit | (fun _ => false) w = false ∧ (fun _ => true) w = true ∧
      (fun _ => false) w = false ∧ (fun _ => false) w = false} : Set Unit) = Set.univ by
    ext w; simp] at this
  rw [show ({w : Unit | (fun _ => Sith) w = Sith} : Set Unit) = Set.univ by ext w; simp] at this
  simp only [Set.inter_self, MeasureTheory.Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ ())] at this
  rw [ENNReal.div_self (by norm_num) (by norm_num)] at this
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)] at this
  simp [ENNReal.toReal_div] at this
  norm_num at this

end Skywalker
