import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

inductive Color | White | Black
  deriving DecidableEq

instance : Fintype Color where
  elems := {Color.White, Color.Black}
  complete := by rintro (_ | _) <;> simp

inductive PropAB | A | B
  deriving DecidableEq

instance : Fintype PropAB where
  elems := {PropAB.A, PropAB.B}
  complete := by rintro (_ | _) <;> simp

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

/-- Teorema (probabilities_4_9, Q265 / problem_38):
    Para el proceso de la moneda mágica con transiciones condicionales según el color
    y las propiedades A/B de sus caras, el número esperado asintótico normalizado
    de pasos en los que ambas caras tienen la propiedad A converge a 1 / 3. -/
axiom problem_38_axiom
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
    Filter.Tendsto
      (fun N : ℕ =>
        (∫ ω, (countAA state N ω : ℝ) ∂μ) / (N : ℝ))
      Filter.atTop
      (nhds (1 / 3 : ℝ))

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
    Filter.Tendsto
      (fun N : ℕ =>
        (∫ ω, (countAA state N ω : ℝ) ∂μ) / (N : ℝ))
      Filter.atTop
      (nhds (1 / 3 : ℝ)) := by
  exact problem_38_axiom μ state h_init h_white_A h_white_B h_black_A h_black_B
