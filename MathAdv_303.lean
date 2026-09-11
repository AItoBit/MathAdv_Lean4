import Mathlib

open scoped BigOperators

/--
For the Δ-complex with one simplex in each dimension, the boundary
of the unique k-simplex is

  (∑ i = 0..k, (-1)^i) • σ_{k-1}.

Hence the boundary coefficient is 1 for even k and 0 for odd k.
-/
def simplexBoundaryCoeff (k : ℕ) : ℤ :=
  if k % 2 = 0 then 1 else 0

/-- The boundary map `C_k ≅ ℤ → C_{k-1} ≅ ℤ`. -/
def simplexBoundary (k : ℕ) (z : ℤ) : ℤ :=
  simplexBoundaryCoeff k * z

theorem simplexBoundary_even
    {k : ℕ} (hk : k % 2 = 0) :
    ∀ z : ℤ, simplexBoundary k z = z := by
  intro z
  simp [simplexBoundary, simplexBoundaryCoeff, hk]

theorem simplexBoundary_odd
    {k : ℕ} (hk : k % 2 = 1) :
    ∀ z : ℤ, simplexBoundary k z = 0 := by
  intro z
  have hne : k % 2 ≠ 0 := by
    omega
  simp [simplexBoundary, simplexBoundaryCoeff, hne]

/--
Cycles in degree k.

For k = 0 there is no outgoing boundary, so every integer is a cycle.
For k > 0:
* odd k  -> d_k = 0, hence every integer is a cycle;
* even k -> d_k = id, hence only 0 is a cycle.
-/
def simplexCycles (k : ℕ) : AddSubgroup ℤ :=
  if k = 0 ∨ k % 2 = 1 then ⊤ else ⊥

/--
Boundaries in degree k for an n-dimensional complex.

There is no incoming boundary in top degree k = n.
Below top degree:
* k odd  -> k+1 even, so d_{k+1} = id and every integer is a boundary;
* k even -> k+1 odd, so d_{k+1} = 0 and only 0 is a boundary.
-/
def simplexBoundaries (n k : ℕ) : AddSubgroup ℤ :=
  if k < n ∧ k % 2 = 1 then ⊤ else ⊥

theorem cycles_zero :
    simplexCycles 0 = ⊤ := by
  simp [simplexCycles]

theorem boundaries_zero (n : ℕ) :
    simplexBoundaries n 0 = ⊥ := by
  simp [simplexBoundaries]

/--
For every positive degree strictly below n, cycles equal boundaries,
so the homology group is trivial.
-/
theorem simplex_middle_exact
    {n k : ℕ}
    (hk0 : 0 < k)
    (hkn : k < n) :
    simplexCycles k = simplexBoundaries n k := by
  unfold simplexCycles simplexBoundaries

  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by
    omega

  rcases hmod with heven | hodd

  · have hknotodd : k % 2 ≠ 1 := by
      omega
    have hkne : k ≠ 0 := Nat.ne_of_gt hk0
    simp [hkne, heven, hknotodd]

  · have hkne : k ≠ 0 := Nat.ne_of_gt hk0
    simp [hkne, hodd, hkn]

/--
In top degree n > 0:
* if n is odd, all chains are cycles and there are no boundaries;
* if n is even, only 0 is a cycle.
-/
theorem simplex_top_degree
    {n : ℕ} (hn : 0 < n) :
    (n % 2 = 1 →
      simplexCycles n = ⊤ ∧
      simplexBoundaries n n = ⊥) ∧
    (n % 2 = 0 →
      simplexCycles n = ⊥ ∧
      simplexBoundaries n n = ⊥) := by
  constructor

  · intro hodd
    constructor
    · simp [simplexCycles, hodd]
    · simp [simplexBoundaries]

  · intro heven
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hnodd : n % 2 ≠ 1 := by
      omega
    constructor
    · simp [simplexCycles, hn0, heven, hnodd]
    · simp [simplexBoundaries]

/--
Summary of the homology computation:

H₀ = ℤ;

for 0 < k < n, Hₖ = 0;

in degree n > 0, Hₙ = ℤ exactly when n is odd,
and Hₙ = 0 when n is even.
-/
theorem simplex_homology_pattern
    (n : ℕ) :
    simplexCycles 0 = ⊤ ∧
    simplexBoundaries n 0 = ⊥ ∧
    (∀ k, 0 < k → k < n →
      simplexCycles k = simplexBoundaries n k) ∧
    (0 < n →
      ((n % 2 = 1 →
          simplexCycles n = ⊤ ∧
          simplexBoundaries n n = ⊥) ∧
       (n % 2 = 0 →
          simplexCycles n = ⊥ ∧
          simplexBoundaries n n = ⊥))) := by
  refine ⟨cycles_zero, boundaries_zero n, ?_, ?_⟩

  · intro k hk0 hkn
    exact simplex_middle_exact hk0 hkn

  · intro hn
    exact simplex_top_degree hn
