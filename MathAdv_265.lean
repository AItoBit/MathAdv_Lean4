import Mathlib

inductive PropAB
  | A
  | B
  deriving DecidableEq

inductive PState
  | AA
  | AB
  | BA
  | BB
  deriving DecidableEq

open scoped BigOperators

def states : Finset PState :=
  {PState.AA, PState.AB, PState.BA, PState.BB}

def transProb : PState → PState → ℚ
  | .AA, .AA => 3 / 4
  | .AA, .BA => 1 / 4

  | .AB, .AB => 1 / 4
  | .AB, .BA => 1 / 2
  | .AB, .BB => 1 / 4

  | .BA, .AB => 1 / 2
  | .BA, .BA => 1 / 4
  | .BA, .BB => 1 / 4

  | .BB, .AA => 1 / 2
  | .BB, .BA => 1 / 4
  | .BB, .BB => 1 / 4

  | _, _ => 0

def stationary : PState → ℚ
  | .AA => 1 / 3
  | .AB => 1 / 5
  | .BA => 3 / 10
  | .BB => 1 / 6

theorem stationary_sum :
    ∑ s ∈ states, stationary s = 1 := by
  norm_num [states, stationary]

theorem transition_row_sum (s : PState) :
    ∑ t ∈ states, transProb s t = 1 := by
  cases s <;>
    norm_num [states, transProb]

theorem stationary_invariant (t : PState) :
    ∑ s ∈ states, stationary s * transProb s t =
      stationary t := by
  cases t <;>
    norm_num [states, stationary, transProb]

theorem stationary_AA :
    stationary PState.AA = 1 / 3 := by
  norm_num [stationary]
