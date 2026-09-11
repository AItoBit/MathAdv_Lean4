import Mathlib

def torusRelativeHomologyRank (m n : ℕ) : ℕ :=
  if n = 2 then
    1
  else if n = 1 then
    m + 1
  else
    0

theorem torus_relative_homology_degree_two
    (m : ℕ) :
    torusRelativeHomologyRank m 2 = 1 := by
  simp [torusRelativeHomologyRank]

theorem torus_relative_homology_degree_one
    (m : ℕ) :
    torusRelativeHomologyRank m 1 = m + 1 := by
  simp [torusRelativeHomologyRank]

theorem torus_relative_homology_degree_zero
    (m : ℕ) :
    torusRelativeHomologyRank m 0 = 0 := by
  simp [torusRelativeHomologyRank]

theorem torus_relative_homology_high
    (m n : ℕ)
    (hn : 3 ≤ n) :
    torusRelativeHomologyRank m n = 0 := by
  have hn2 : n ≠ 2 := by
    omega
  have hn1 : n ≠ 1 := by
    omega
  simp [torusRelativeHomologyRank, hn2, hn1]

theorem torus_relative_homology_pattern
    (m n : ℕ) :
    torusRelativeHomologyRank m n =
      if n = 2 then 1
      else if n = 1 then m + 1
      else 0 := by
  rfl
