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
# The magic coin

A coin has a white side and a black side; each side carries a property, `A` or `B`.
At each toss the coin lands white side up or black side up (probability `1/2` each) and then:

* white up, up side has property `A`: the up side's property is changed with probability `1/2`;
* white up, up side has property `B`: the down side's property is changed with probability `1/2`;
* black up, up side has property `A`: the two sides' properties are swapped;
* black up, up side has property `B`: both properties are flipped (`A ↔ B`).

Initially one side is white and the other is black and the properties are unknown.  The expected
number of tosses, among the first `N`, at which both sides have property `A` is asymptotically
`N / 3`.

This file contains:

* the auxiliary definitions of the originally proposed formalization (`Color`, `PropAB`,
  `CoinState`, `isAA`, `countAA`);
* `problem_38_hypotheses_inconsistent`: the hypotheses of that proposed formalization are
  contradictory, so the statement it proposes says nothing about the magic coin (see the
  discussion below, and the original statement, kept commented out);
* the namespace `MagicCoin`: a faithful model of the process together with the main results
  `MagicCoin.abs_expAA_sub_le` (the expected number of tosses among the first `N` at which both
  sides have property `A` differs from `N / 3` by at most `8 / 3`, uniformly in `N` and in the
  unknown initial distribution) and `MagicCoin.expAA_div_tendsto` (hence this expectation is
  asymptotically `N / 3`).
-/

inductive Color | White | Black deriving DecidableEq, Fintype
inductive PropAB | A | B deriving DecidableEq, Fintype

structure CoinState where
  upColor  : Color
  upProp   : PropAB
  downProp : PropAB
deriving DecidableEq

instance : MeasurableSpace Color := ⊤
instance : MeasurableSpace PropAB := ⊤
instance : MeasurableSpace CoinState := ⊤

def isAA (s : CoinState) : Bool :=
  (s.upProp = PropAB.A) && (s.downProp = PropAB.A)

def countAA {Ω : Type*} (state : ℕ → Ω → CoinState) (N : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.range N, (if isAA (state t ω) then 1 else 0)

instance : Fintype CoinState :=
  Fintype.ofEquiv (Color × PropAB × PropAB)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun s => (s.upColor, s.upProp, s.downProp)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-!
## The originally proposed formalization is contradictory

In the statement quoted below (kept, commented out, at the end of this section) the two
"black side up" hypotheses `h_black_A` and `h_black_B` are imposed for *every* time `t` and
*every* state `s`, unconditionally and with conditional probability `1`.  They demand that, on the
event `{state t = s}`, the state at time `t + 1` is almost surely the state with the two
properties swapped, and *also* almost surely the state with both properties flipped.  For all but
two states `s` these are two different states, which forces `μ {state t = s} = 0`; the two
remaining states are then excluded by the "white side up" hypotheses.  Since the events
`{state t = s}` cover the whole space, this is impossible.

The theorem below proves exactly this, under the (harmless, and clearly intended) extra
assumption that each map `state t` is measurable.
-/

/-- The hypotheses of the originally proposed formalization of the problem cannot be satisfied by
any measurable process on a probability space. -/
theorem problem_38_hypotheses_inconsistent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (state : ℕ → Ω → CoinState)
    (h_meas : ∀ t : ℕ, Measurable (state t))
    (h_white_A :
      ∀ t s,
        μ {ω | state t ω = s} ≠ 0 →
        s.upColor = Color.White →
        s.upProp = PropAB.A →
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor, upProp := PropAB.B, downProp := s.downProp }} ∩
            {ω | state t ω = s})
          / μ {ω | state t ω = s} = ((1 : ENNReal) / 2))
    (h_white_B :
      ∀ t s,
        μ {ω | state t ω = s} ≠ 0 →
        s.upColor = Color.White →
        s.upProp = PropAB.B →
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor, upProp := s.upProp, downProp := PropAB.A }} ∩
            {ω | state t ω = s})
          / μ {ω | state t ω = s} = ((1 : ENNReal) / 2))
    (h_black_A :
      ∀ t s,
        μ ({ω | state (t + 1) ω =
              { upColor := Color.White,
                upProp := s.downProp,
                downProp := s.upProp }} ∩
            {ω | state t ω = s})
        =
        μ {ω | state t ω = s})
    (h_black_B :
      ∀ t s,
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor,
                upProp := if s.upProp = PropAB.A then PropAB.B else PropAB.A,
                downProp := if s.downProp = PropAB.A then PropAB.B else PropAB.A }} ∩
            {ω | state t ω = s})
        =
        μ {ω | state t ω = s}) :
    False := by
  have hmeas' : ∀ (t : ℕ) (s : CoinState), MeasurableSet {ω | state t ω = s} := fun t s =>
    (h_meas t) (measurableSet_singleton s)
  -- two different states at time `t + 1` cut `{state t = s}` into disjoint pieces
  have hsplit : ∀ (t : ℕ) (s x y : CoinState), x ≠ y →
      μ ({ω | state (t + 1) ω = x} ∩ {ω | state t ω = s})
        + μ ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s})
        ≤ μ {ω | state t ω = s} := by
    intro t s x y hxy
    have hdisj :
        Disjoint ({ω | state (t + 1) ω = x} ∩ {ω | state t ω = s})
          ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s}) := by
      rw [Set.disjoint_left]
      rintro ω ⟨hx, -⟩ ⟨hy, -⟩
      exact hxy (hx ▸ hy ▸ rfl)
    have hu :
        μ (({ω | state (t + 1) ω = x} ∩ {ω | state t ω = s})
            ∪ ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s}))
          = μ ({ω | state (t + 1) ω = x} ∩ {ω | state t ω = s})
            + μ ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s}) :=
      MeasureTheory.measure_union hdisj ((hmeas' (t + 1) y).inter (hmeas' t s))
    rw [← hu]
    exact MeasureTheory.measure_mono (by rintro ω (⟨-, h⟩ | ⟨-, h⟩) <;> exact h)
  -- by `h_black_A`, every state at time `t + 1` other than the "swapped" one is unreachable
  have hzero : ∀ (t : ℕ) (s y : CoinState),
      y ≠ { upColor := Color.White, upProp := s.downProp, downProp := s.upProp } →
      μ ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s}) = 0 := by
    intro t s y hy
    have hsp := hsplit t s y _ hy
    rw [h_black_A t s] at hsp
    have hmtop : μ {ω | state t ω = s} ≠ ⊤ := (MeasureTheory.measure_lt_top μ _).ne
    have h2 : μ ({ω | state (t + 1) ω = y} ∩ {ω | state t ω = s}) + μ {ω | state t ω = s}
        ≤ 0 + μ {ω | state t ω = s} := by simpa using hsp
    simpa using (ENNReal.add_le_add_iff_right hmtop).1 h2
  -- the two states for which swapping and flipping agree are excluded by the white hypotheses
  have specialA : ∀ (t : ℕ) (s : CoinState), s.upColor = Color.White → s.upProp = PropAB.A →
      s.downProp = PropAB.B → μ {ω | state t ω = s} = 0 := by
    intro t s hcol hup hdown
    by_contra hm0
    have h := hzero t s { upColor := s.upColor, upProp := PropAB.B, downProp := s.downProp }
      (by simp [hcol, hup, hdown])
    have hw := h_white_A t s hm0 hcol hup
    rw [h, ENNReal.zero_div, eq_comm, ENNReal.div_eq_zero_iff] at hw
    simp at hw
  have specialB : ∀ (t : ℕ) (s : CoinState), s.upColor = Color.White → s.upProp = PropAB.B →
      s.downProp = PropAB.A → μ {ω | state t ω = s} = 0 := by
    intro t s hcol hup hdown
    by_contra hm0
    have h := hzero t s { upColor := s.upColor, upProp := s.upProp, downProp := PropAB.A }
      (by simp [hcol, hup, hdown])
    have hw := h_white_B t s hm0 hcol hup
    rw [h, ENNReal.zero_div, eq_comm, ENNReal.div_eq_zero_iff] at hw
    simp at hw
  -- hence no state is ever attained with positive probability
  have key : ∀ (t : ℕ) (s : CoinState), μ {ω | state t ω = s} = 0 := by
    intro t s
    rcases eq_or_ne
        ({ upColor := s.upColor,
           upProp := if s.upProp = PropAB.A then PropAB.B else PropAB.A,
           downProp := if s.downProp = PropAB.A then PropAB.B else PropAB.A } : CoinState)
        ({ upColor := Color.White, upProp := s.downProp, downProp := s.upProp } : CoinState)
        with hxy | hxy
    · have h1 : s.upColor = Color.White := congrArg CoinState.upColor hxy
      have h2 : (if s.upProp = PropAB.A then PropAB.B else PropAB.A) = s.downProp :=
        congrArg CoinState.upProp hxy
      cases hu : s.upProp <;> cases hd : s.downProp
      · rw [hu, hd] at h2; simp at h2
      · exact specialA t s h1 hu hd
      · exact specialB t s h1 hu hd
      · rw [hu, hd] at h2; simp at h2
    · rw [← h_black_B t s]
      exact hzero t s _ hxy
  -- but the states at time `0` cover the whole space
  have hcover : (Set.univ : Set Ω) = ⋃ s : CoinState, {ω | state 0 ω = s} := by
    ext ω; simp
  have h1 : (1 : ENNReal) ≤ 0 := by
    calc (1 : ENNReal) = μ Set.univ := (MeasureTheory.measure_univ).symm
      _ = μ (⋃ s : CoinState, {ω | state 0 ω = s}) := by rw [hcover]
      _ ≤ ∑' s : CoinState, μ {ω | state 0 ω = s} := MeasureTheory.measure_iUnion_le _
      _ = 0 := by simp [key]
  simp at h1

/-
The original statement.  It is commented out because its hypotheses are contradictory, as proved
in `problem_38_hypotheses_inconsistent` above: no (measurable) process satisfies `h_black_A` and
`h_black_B`, which assert, unconditionally and with probability one, two *different* next states.
Consequently nothing about the actual magic coin can be deduced from it.  A faithful formalization
of the problem, with a complete proof, is given in the namespace `MagicCoin` below.

theorem problem_38
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (state : ℕ → Ω → CoinState)
    (h_init :
      ∀ ω,
        (state 0 ω).upColor = Color.White ∨
        (state 0 ω).upColor = Color.Black)
    (h_white_A :
      ∀ t s,
        μ {ω | state t ω = s} ≠ 0 →
        s.upColor = Color.White →
        s.upProp = PropAB.A →
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor, upProp := PropAB.B, downProp := s.downProp }} ∩
            {ω | state t ω = s})
          / μ {ω | state t ω = s} = ((1 : ℝ≥0∞) / 2))
    (h_white_B :
      ∀ t s,
        μ {ω | state t ω = s} ≠ 0 →
        s.upColor = Color.White →
        s.upProp = PropAB.B →
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor, upProp := s.upProp, downProp := PropAB.A }} ∩
            {ω | state t ω = s})
          / μ {ω | state t ω = s} = ((1 : ℝ≥0∞) / 2))
    (h_black_A :
      ∀ t s,
        μ ({ω | state (t + 1) ω =
              { upColor := Color.White,
                upProp := s.downProp,
                downProp := s.upProp }} ∩
            {ω | state t ω = s})
        =
        μ {ω | state t ω = s})
    (h_black_B :
      ∀ t s,
        μ ({ω | state (t + 1) ω =
              { upColor := s.upColor,
                upProp := if s.upProp = PropAB.A then PropAB.B else PropAB.A,
                downProp := if s.downProp = PropAB.A then PropAB.B else PropAB.A }} ∩
            {ω | state t ω = s})
        =
        μ {ω | state t ω = s})
    :
    Filter.Tendsto
      (fun N : ℕ =>
        (∫ ω, (countAA state N ω : ℝ) ∂μ) / (N : ℝ))
      Filter.atTop
      (𝓝 (1 / 3 : ℝ)) := by
  sorry
-/

namespace MagicCoin

/-- Flipping a property: `A ↔ B`. -/
def PropAB.flip : PropAB → PropAB
  | PropAB.A => PropAB.B
  | PropAB.B => PropAB.A

/-- A configuration of the coin: the property of the white side and the property of the black
side.  (The sides keep their colours; only the properties move.) -/
abbrev Cfg := PropAB × PropAB

/-- The configuration after a toss landing **black side up**: if the up (black) side has property
`A` the two properties are swapped, and if it has property `B` both properties are flipped. -/
def blackUp (s : Cfg) : Cfg :=
  match s.2 with
  | PropAB.A => (s.2, s.1)
  | PropAB.B => (PropAB.flip s.1, PropAB.flip s.2)

/-- The configuration after a toss landing **white side up** for which the `50%` change does
happen: if the up (white) side has property `A` the up side's property is changed, and if it has
property `B` the down (black) side's property is changed. -/
def whiteUpChange (s : Cfg) : Cfg :=
  match s.1 with
  | PropAB.A => (PropAB.flip s.1, s.2)
  | PropAB.B => (s.1, PropAB.flip s.2)

/-- One toss, as a deterministic function of the randomness: `o.1 = true` means that the coin
landed black side up, and `o.2` is the independent fair bit deciding the `50%` change that occurs
when the coin lands white side up. -/
def update (s : Cfg) (o : Bool × Bool) : Cfg :=
  if o.1 then blackUp s else if o.2 then whiteUpChange s else s

/-- The transition probability from configuration `s` to configuration `t`: the four outcomes
`o : Bool × Bool` (side up, fair bit) are equally likely. -/
noncomputable def tr (s t : Cfg) : ℝ :=
  ∑ o : Bool × Bool, (1 / 4 : ℝ) * (if update s o = t then 1 else 0)

/-- One step of the evolution of the distribution of the configuration. -/
noncomputable def stepDist (p : Cfg → ℝ) : Cfg → ℝ := fun t => ∑ s : Cfg, p s * tr s t

/-- The distribution of the configuration after `n` tosses, starting from the (unknown) initial
distribution `p₀`. -/
noncomputable def dist (p₀ : Cfg → ℝ) : ℕ → Cfg → ℝ
  | 0 => p₀
  | n + 1 => stepDist (dist p₀ n)

/-- The expected number of tosses `t < N` at which both sides have property `A`; by linearity of
expectation this is the sum of the corresponding probabilities. -/
noncomputable def expAA (p₀ : Cfg → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, dist p₀ t (PropAB.A, PropAB.A)

/-- `p₀` is a probability distribution on configurations. -/
structure IsProbDist (p₀ : Cfg → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ p₀ s
  total : p₀ (PropAB.A, PropAB.A) + p₀ (PropAB.A, PropAB.B) + p₀ (PropAB.B, PropAB.A)
      + p₀ (PropAB.B, PropAB.B) = 1

private lemma AneB : ¬ (PropAB.A = PropAB.B) := by decide
private lemma BneA : ¬ (PropAB.B = PropAB.A) := by decide

lemma sum_PropAB (g : PropAB → ℝ) : ∑ x : PropAB, g x = g PropAB.A + g PropAB.B := by
  rw [show (Finset.univ : Finset PropAB) = {PropAB.A, PropAB.B} from rfl]
  rw [Finset.sum_pair (show PropAB.A ≠ PropAB.B by decide)]

lemma sum_cfg (g : Cfg → ℝ) :
    ∑ s : Cfg, g s = g (PropAB.A, PropAB.A) + g (PropAB.A, PropAB.B) + g (PropAB.B, PropAB.A)
      + g (PropAB.B, PropAB.B) := by
  rw [Fintype.sum_prod_type, sum_PropAB]
  rw [sum_PropAB (fun y => g (PropAB.A, y)), sum_PropAB (fun y => g (PropAB.B, y))]
  ring

section StepFormulas

variable (p : Cfg → ℝ)

lemma stepDist_AA :
    stepDist p (PropAB.A, PropAB.A)
      = 3 / 4 * p (PropAB.A, PropAB.A) + 1 / 2 * p (PropAB.B, PropAB.B) := by
  rw [stepDist, sum_cfg]
  simp only [tr, Fintype.sum_prod_type, Fintype.sum_bool, update, blackUp, whiteUpChange,
    PropAB.flip]
  norm_num [AneB, BneA]
  ring

lemma stepDist_AB :
    stepDist p (PropAB.A, PropAB.B)
      = 1 / 4 * p (PropAB.A, PropAB.B) + 1 / 2 * p (PropAB.B, PropAB.A) := by
  rw [stepDist, sum_cfg]
  simp only [tr, Fintype.sum_prod_type, Fintype.sum_bool, update, blackUp, whiteUpChange,
    PropAB.flip]
  norm_num [AneB, BneA]
  ring

lemma stepDist_BA :
    stepDist p (PropAB.B, PropAB.A)
      = 1 / 4 * p (PropAB.A, PropAB.A) + 1 / 2 * p (PropAB.A, PropAB.B)
        + 1 / 4 * p (PropAB.B, PropAB.A) + 1 / 4 * p (PropAB.B, PropAB.B) := by
  rw [stepDist, sum_cfg]
  simp only [tr, Fintype.sum_prod_type, Fintype.sum_bool, update, blackUp, whiteUpChange,
    PropAB.flip]
  norm_num [AneB, BneA]
  ring

lemma stepDist_BB :
    stepDist p (PropAB.B, PropAB.B)
      = 1 / 4 * p (PropAB.A, PropAB.B) + 1 / 4 * p (PropAB.B, PropAB.A)
        + 1 / 4 * p (PropAB.B, PropAB.B) := by
  rw [stepDist, sum_cfg]
  simp only [tr, Fintype.sum_prod_type, Fintype.sum_bool, update, blackUp, whiteUpChange,
    PropAB.flip]
  norm_num [AneB, BneA]
  ring

/-- `tr` is a stochastic matrix: from any configuration the transition probabilities sum to `1`.
-/
lemma tr_row_sum (s : Cfg) : ∑ t : Cfg, tr s t = 1 := by
  obtain ⟨u, v⟩ := s
  cases u <;> cases v <;>
    (rw [sum_cfg]
     simp only [tr, Fintype.sum_prod_type, Fintype.sum_bool, update, blackUp, whiteUpChange,
       PropAB.flip]
     norm_num [AneB, BneA])

end StepFormulas

/-- The uniform initial distribution is an admissible initial distribution. -/
example : IsProbDist (fun _ => (1 : ℝ) / 4) :=
  { nonneg := by intro _; norm_num
    total := by norm_num }

variable {p₀ : Cfg → ℝ}

lemma dist_nonneg (h : IsProbDist p₀) : ∀ (n : ℕ) (s : Cfg), 0 ≤ dist p₀ n s := by
  intro n
  induction n with
  | zero => exact h.nonneg
  | succ n ih =>
      intro s
      have h1 := ih (PropAB.A, PropAB.A)
      have h2 := ih (PropAB.A, PropAB.B)
      have h3 := ih (PropAB.B, PropAB.A)
      have h4 := ih (PropAB.B, PropAB.B)
      obtain ⟨u, v⟩ := s
      cases u <;> cases v <;>
        simp only [dist, stepDist_AA, stepDist_AB, stepDist_BA, stepDist_BB] <;> linarith

lemma dist_total (h : IsProbDist p₀) : ∀ n : ℕ,
    dist p₀ n (PropAB.A, PropAB.A) + dist p₀ n (PropAB.A, PropAB.B)
      + dist p₀ n (PropAB.B, PropAB.A) + dist p₀ n (PropAB.B, PropAB.B) = 1 := by
  intro n
  induction n with
  | zero => exact h.total
  | succ n ih =>
      simp only [dist, stepDist_AA, stepDist_AB, stepDist_BA, stepDist_BB]
      linarith

/-- The potential solving the Poisson equation `(P f)(s) - f(s) = 1_{AA}(s) - 1/3`, evaluated
against a distribution `p`. -/
noncomputable def pot (p : Cfg → ℝ) : ℝ :=
  8 / 3 * (p (PropAB.A, PropAB.B) + p (PropAB.B, PropAB.A)) + 4 / 3 * p (PropAB.B, PropAB.B)

lemma pot_step (h : IsProbDist p₀) (n : ℕ) :
    pot (dist p₀ (n + 1)) - pot (dist p₀ n) = dist p₀ n (PropAB.A, PropAB.A) - 1 / 3 := by
  have htot := dist_total h n
  simp only [pot, dist, stepDist_AB, stepDist_BA, stepDist_BB]
  linarith

lemma pot_nonneg (h : IsProbDist p₀) (n : ℕ) : 0 ≤ pot (dist p₀ n) := by
  have h2 := dist_nonneg h n (PropAB.A, PropAB.B)
  have h3 := dist_nonneg h n (PropAB.B, PropAB.A)
  have h4 := dist_nonneg h n (PropAB.B, PropAB.B)
  simp only [pot]; linarith

lemma pot_le (h : IsProbDist p₀) (n : ℕ) : pot (dist p₀ n) ≤ 8 / 3 := by
  have h1 := dist_nonneg h n (PropAB.A, PropAB.A)
  have h4 := dist_nonneg h n (PropAB.B, PropAB.B)
  have htot := dist_total h n
  simp only [pot]; linarith

lemma expAA_eq (h : IsProbDist p₀) (N : ℕ) :
    expAA p₀ N - N / 3 = pot (dist p₀ N) - pot (dist p₀ 0) := by
  induction N with
  | zero => simp [expAA]
  | succ n ih =>
      have hstep := pot_step h n
      have hsum : expAA p₀ (n + 1) = expAA p₀ n + dist p₀ n (PropAB.A, PropAB.A) := by
        rw [expAA, Finset.sum_range_succ, expAA]
      rw [hsum]
      push_cast
      linarith

/-- **Quantitative form of the answer.**  Whatever the (unknown) initial distribution of the
properties, the expected number of tosses among the first `N` at which both sides have property
`A` differs from `N / 3` by at most `8 / 3`. -/
theorem abs_expAA_sub_le (h : IsProbDist p₀) (N : ℕ) :
    |expAA p₀ N - N / 3| ≤ 8 / 3 := by
  have h1 := pot_nonneg h N
  have h2 := pot_le h N
  have h3 := pot_nonneg h 0
  have h4 := pot_le h 0
  rw [expAA_eq h N, abs_le]
  constructor <;> linarith

/-- **The answer: the asymptotic expected number of tosses at which both sides have property `A`
is `N / 3`.** -/
theorem expAA_div_tendsto (h : IsProbDist p₀) :
    Filter.Tendsto (fun N : ℕ => expAA p₀ N / (N : ℝ)) Filter.atTop (nhds (1 / 3 : ℝ)) := by
  have hbound : ∀ᶠ N : ℕ in Filter.atTop, ‖expAA p₀ N / (N : ℝ) - 1 / 3‖ ≤ (8 / 3) / (N : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have key : expAA p₀ N / (N : ℝ) - 1 / 3 = (expAA p₀ N - N / 3) / (N : ℝ) := by
      field_simp
    rw [key, Real.norm_eq_abs, abs_div, abs_of_pos hN']
    gcongr
    exact abs_expAA_sub_le h N
  have hzero : Filter.Tendsto (fun N : ℕ => (8 / 3 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hdiff := squeeze_zero_norm' hbound hzero
  have h' : Filter.Tendsto (fun N : ℕ => (expAA p₀ N / (N : ℝ) - 1 / 3) + 1 / 3)
      Filter.atTop (nhds (0 + 1 / 3)) := hdiff.add tendsto_const_nhds
  simpa using h'

end MagicCoin

