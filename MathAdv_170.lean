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
# Bishop–Gromov volume rigidity (Petersen, Ch. 9)

**Statement.** If `(M,g)` satisfies `Ric ≥ (n-1)k` and `vol B(p,R) = v(n,k,R)` (the volume of the
ball of radius `R` in the simply connected model space of constant curvature `k`), then `g` has
constant curvature `k` on `B(p,R)`.

**Correct reasoning: option (c).** One applies the Bishop–Gromov volume comparison theorem: the
ratio `vol B(p,r) / v(n,k,r)` is non-increasing in `r` and is `≤ 1`; equality for the single radius
`R` therefore forces equality for every `r ≤ R`, i.e. equality throughout the comparison argument.
Equality in the underlying pointwise (Riccati/Jacobi field) comparison then forces the radial
sectional curvatures to equal `k` and the geodesic spheres to be totally umbilic, so the metric is
the constant-curvature-`k` metric on `B(p,R)`.

Options (a), (b), (d) are wrong: Hopf–Rinow is a completeness statement and says nothing about
curvature; constant scalar curvature does not imply constant sectional curvature; and comparing
with the Euclidean ball would only be relevant for `k = 0`.

## Contents of this file

* The data structure `GeomData` and the predicates supplied with the problem.
* `Petersen_9_3_counterexample`: the literal Lean statement supplied with the problem is **not
  provable** — at that level of abstraction the model volume function `v` is an arbitrary
  parameter and `G.sec` is arbitrary data unrelated to `G.μ`, so the statement is false. A
  concrete counterexample is given.
* `volume_eq_of_ball_volume_eq`: the genuine content of the equality case of Bishop–Gromov that
  *can* be proved from the comparison inequalities, namely that equality at radius `R` propagates
  to every radius `0 < r ≤ R`.
* `Petersen_9_3_corrected`: a faithful version of the exercise in which the geometric inputs
  (Bishop's inequality, Bishop–Gromov monotonicity, and the pointwise rigidity supplied by the
  equality case of the Riccati comparison) are stated as hypotheses.
* `Petersen_9_3_answer`: the multiple-choice answer, `(c)`.
-/

/-- Abstract bundle of the metric-measure data of a Riemannian manifold that the statement
refers to: the distance function, the Riemannian measure, the (radial) Ricci curvature and the
sectional curvature, the last two recorded as plain functions of the point. -/
structure GeomData (M : Type*) [MeasurableSpace M] where
  dist : M → M → ℝ
  μ    : MeasureTheory.Measure M
  Ric  : M → ℝ
  sec  : M → ℝ

/-- The metric ball of radius `R` around `p`. -/
def ball {M : Type*} [MeasurableSpace M] (G : GeomData M) (p : M) (R : ℝ) : Set M :=
  {x : M | G.dist x p < R}

/-- The volume of a set, as a real number. -/
def vol {M : Type*} [MeasurableSpace M] (G : GeomData M) (s : Set M) : ℝ :=
  (G.μ s).toReal

/-- `Ric ≥ (n-1) k`. -/
def RicciLowerBound {M : Type*} [MeasurableSpace M] (G : GeomData M) (n : ℕ) (k : ℝ) : Prop :=
  ∀ x : M, (n - 1 : ℝ) * k ≤ G.Ric x

/-- The sectional curvature is constantly `k` on `s`. -/
def SecConstOn {M : Type*} [MeasurableSpace M] (G : GeomData M) (s : Set M) (k : ℝ) : Prop :=
  ∀ x : M, x ∈ s → G.sec x = k

/-
The statement exactly as supplied:

```
theorem Petersen_9_3
  {M : Type*} [MeasurableSpace M]
  (G : GeomData M)
  (n : ℕ) (k R : ℝ) (p : M)
  (v : ℕ → ℝ → ℝ → ℝ)
  (hR : 0 < R)
  (hRic : RicciLowerBound G n k)
  (hVolEq : vol G (ball G p R) = v n k R) :
  SecConstOn G (ball G p R) k
```

It is **false**, and is therefore commented out here (see `Petersen_9_3_counterexample` below for a
disproof).  The reason is that in this abstract setting nothing ties the four fields of `GeomData`
to one another — `G.sec` is arbitrary data, unrelated to `G.dist` and `G.μ` — and the model volume
function `v` is a universally quantified parameter, so the hypothesis `vol B(p,R) = v n k R`
carries no information: `v` can simply be chosen to match whatever `vol B(p,R)` happens to be.
-/

/-- The literal statement of the exercise, at the given level of abstraction, is refutable: one
may take a one-point space, `k = 1`, `sec ≡ 0`, and choose the "model volume function" `v` to be
the constant function matching the actual volume. -/
theorem Petersen_9_3_counterexample :
    ¬ (∀ {M : Type} [MeasurableSpace M] (G : GeomData M) (n : ℕ) (k R : ℝ) (p : M)
        (v : ℕ → ℝ → ℝ → ℝ), 0 < R → RicciLowerBound G n k →
        vol G (ball G p R) = v n k R → SecConstOn G (ball G p R) k) := by
  intro h
  classical
  let G : GeomData Unit :=
    { dist := fun _ _ => 0
      μ := (0 : MeasureTheory.Measure Unit)
      Ric := fun _ => 1
      sec := fun _ => 0 }
  have hRic : RicciLowerBound G 2 1 := by
    intro x
    norm_num [G]
  have hVol : vol G (ball G () 1) = (fun (_ : ℕ) (_ _ : ℝ) => (0 : ℝ)) 2 1 1 := by
    simp [vol, G]
  have := h G 2 1 1 () (fun _ _ _ => 0) one_pos hRic hVol ()
    (by simp [ball, G])
  simp [G] at this

/-- **Equality propagation in Bishop–Gromov.** Assume the two comparison facts supplied by the
Bishop–Gromov theorem under `Ric ≥ (n-1)k`:

* `hBishop`: `vol B(p,r) ≤ v(n,k,r)` for all `0 < r`;
* `hMono`: the ratio `vol B(p,r) / v(n,k,r)` is non-increasing in `r`;

together with positivity of the model volumes.  If equality holds at the single radius `R`, then it
holds at every radius `0 < r ≤ R`; i.e. equality holds throughout the comparison argument.  This is
the step that makes option (c) work. -/
theorem volume_eq_of_ball_volume_eq
    {M : Type*} [MeasurableSpace M] (G : GeomData M) (n : ℕ) (k R : ℝ) (p : M)
    (v : ℕ → ℝ → ℝ → ℝ) (hR : 0 < R)
    (hvpos : ∀ r : ℝ, 0 < r → 0 < v n k r)
    (hBishop : ∀ r : ℝ, 0 < r → vol G (ball G p r) ≤ v n k r)
    (hMono : ∀ r s : ℝ, 0 < r → r ≤ s →
      vol G (ball G p s) / v n k s ≤ vol G (ball G p r) / v n k r)
    (hVolEq : vol G (ball G p R) = v n k R) :
    ∀ r : ℝ, 0 < r → r ≤ R → vol G (ball G p r) = v n k r := by
  intro r hr hrR
  have hvr : 0 < v n k r := hvpos r hr
  have hvR : 0 < v n k R := hvpos R hR
  have hratio : vol G (ball G p R) / v n k R ≤ vol G (ball G p r) / v n k r :=
    hMono r R hr hrR
  have hone : (1 : ℝ) ≤ vol G (ball G p r) / v n k r := by
    rw [hVolEq, div_self (ne_of_gt hvR)] at hratio
    exact hratio
  have hge : v n k r ≤ vol G (ball G p r) := by
    rw [le_div_iff₀ hvr, one_mul] at hone
    exact hone
  exact le_antisymm (hBishop r hr) hge

/-- **A faithful form of the exercise.**  Under `Ric ≥ (n-1)k`, the Bishop–Gromov comparison
inequalities, and the pointwise rigidity provided by the equality case of the Riccati/Jacobi field
comparison (`hRigidity`: if the volume of *every* ball `B(p,r)`, `0 < r ≤ R`, agrees with the model
value, then the sectional curvature is `k` on `B(p,R)`), volume equality at the single radius `R`
forces the metric to have constant curvature `k` on `B(p,R)`.

The hypothesis `hRic` is the one under which the comparison inputs `hBishop`/`hMono` hold; it is
kept because the exercise states it, although the formal derivation below uses it only through
those inputs. -/
theorem Petersen_9_3_corrected
    {M : Type*} [MeasurableSpace M] (G : GeomData M) (n : ℕ) (k R : ℝ) (p : M)
    (v : ℕ → ℝ → ℝ → ℝ) (hR : 0 < R)
    (hRic : RicciLowerBound G n k)
    (hvpos : ∀ r : ℝ, 0 < r → 0 < v n k r)
    (hBishop : ∀ r : ℝ, 0 < r → vol G (ball G p r) ≤ v n k r)
    (hMono : ∀ r s : ℝ, 0 < r → r ≤ s →
      vol G (ball G p s) / v n k s ≤ vol G (ball G p r) / v n k r)
    (hRigidity : (∀ r : ℝ, 0 < r → r ≤ R → vol G (ball G p r) = v n k r) →
      SecConstOn G (ball G p R) k)
    (hVolEq : vol G (ball G p R) = v n k R) :
    SecConstOn G (ball G p R) k := by
  have _ := hRic
  exact hRigidity (volume_eq_of_ball_volume_eq G n k R p v hR hvpos hBishop hMono hVolEq)

/-- The four candidate justifications offered in the multiple-choice question. -/
inductive PetersenReason
  | hopfRinow
  | scalarCurvature
  | bishopGromov
  | euclideanComparison
  deriving DecidableEq

/-- The reasoning selected as correct: option (c). -/
def PetersenChosenReason : PetersenReason := PetersenReason.bishopGromov

/-- The correct reasoning is **(c)**: apply the Bishop–Gromov volume comparison theorem; equality
for one ball forces equality throughout the comparison argument, hence the radial sectional
curvatures equal `k` and the geodesic spheres are totally umbilic.  The other three options are
rejected. -/
theorem Petersen_9_3_answer :
    PetersenChosenReason = PetersenReason.bishopGromov ∧
      PetersenChosenReason ≠ PetersenReason.hopfRinow ∧
      PetersenChosenReason ≠ PetersenReason.scalarCurvature ∧
      PetersenChosenReason ≠ PetersenReason.euclideanComparison := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide
