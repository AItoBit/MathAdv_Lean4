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

set_option grind.warning false

/-!
# Steady temperature at the centre of a square plate

Two adjacent edges of a unit square plate are kept at `0`, the other two at `100`.
The classical model is the Dirichlet problem for Laplace's equation on the square
(steady temperatures in a rectangular plate).

This file contains:

* the sets describing the square and its four edges;
* the mean–value formulation `HarmonicOn` of harmonicity;
* a proof that the literal statement `brown_7b` proposed for this problem is **false**
  (theorem `brown_7b_not_exists`): its boundary conditions force a function that is
  continuous on the whole closed square to take both the value `0` and the value `100`
  at the corner `(1,0)`;
* a corrected formulation `SteadyTemp` (boundary values prescribed only on the *open*
  edges, continuity required away from the four corners, and genuine harmonicity), for
  which the symmetry `(x,y) ↦ (1-x,1-y)` is proved to preserve the problem
  (`steadyTemp_symm`) and consequently the temperature at the centre of the plate is
  `50`, **not** `25` (`steadyTemp_center_eq_fifty`);
* a proof that, with the harmonicity clause left vacuous, the boundary data does not
  determine the value at the centre at all (`exists_boundary_data_center_25`).
-/

/-- The closed unit square plate. -/
def Ω : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

def left : Set (ℝ × ℝ) :=
  {p | p.1 = 0 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

def right : Set (ℝ × ℝ) :=
  {p | p.1 = 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

def bottom : Set (ℝ × ℝ) :=
  {p | p.2 = 0 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}

def top : Set (ℝ × ℝ) :=
  {p | p.2 = 1 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}

/-- Average of `u` over the circle of radius `r` centred at `p`. -/
noncomputable def circleAvg (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (r : ℝ) :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0)..(2 * Real.pi),
      u (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ)

/-- Harmonicity in the sense of the mean value property. -/
def HarmonicOn (u : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ D, ∀ r > 0,
    Metric.ball p r ⊆ D →
      u p = circleAvg u p r

/-
The originally proposed statement was

theorem brown_7b :
  ∃ u : (ℝ × ℝ) → ℝ,
    ContinuousOn u (closure Ω) ∧
    (∀ p ∈ interior Ω, True) ∧
    (∀ p ∈ left ∩ Ω,   u p = 0) ∧
    (∀ p ∈ bottom ∩ Ω, u p = 0) ∧
    (∀ p ∈ right ∩ Ω,  u p = 100) ∧
    (∀ p ∈ top ∩ Ω,    u p = 100) ∧
    u (1/2, 1/2) = 25

It is false, and is proved false below (`brown_7b_not_exists`).  Two things go wrong.

* The boundary conditions are inconsistent with continuity on the *closed* square: the
  edge `right` contains the corner `(1,0)`, where `u` is required to be `100`, while `u`
  is required to vanish on `bottom = {(x,0) : 0 < x < 1}`, whose closure contains `(1,0)`.
  (This is not merely a bookkeeping problem: the boundary data of this heat problem really
  is discontinuous at the two corners where a `0`-edge meets a `100`-edge, so no solution
  is continuous up to those corners.)
* The harmonicity requirement was rendered as `∀ p ∈ interior Ω, True`, which is vacuous;
  with it, the value at the centre is not pinned down at all.  With genuine harmonicity,
  the symmetry `(x,y) ↦ (1-x,1-y)` (which exchanges the `0`-edges with the `100`-edges)
  forces the value `50` at the centre, not `25`.
-/

/-- `bottom ∩ Ω` is the open bottom edge of the square. -/
theorem bottom_inter_Omega : bottom ∩ Ω = Set.Ioo (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) := by
  ext p
  constructor
  · rintro ⟨⟨h2, h1⟩, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_singleton_iff] at h2
    refine ⟨⟨h2, h1⟩, ⟨le_of_lt h1.1, le_of_lt h1.2⟩, ?_⟩
    simp [h2]

/-- The corner `(1,0)` lies in the closure of the open bottom edge. -/
theorem corner_mem_closure_bottom : ((1 : ℝ), (0 : ℝ)) ∈ closure (bottom ∩ Ω) := by
  rw [bottom_inter_Omega, closure_prod_eq, closure_Ioo (by norm_num : (0:ℝ) ≠ 1),
    closure_singleton]
  exact ⟨by norm_num, rfl⟩

theorem closure_Omega : closure Ω = Ω :=
  IsClosed.closure_eq (isClosed_Icc.prod isClosed_Icc)

/-- The proposed statement of the problem is false: no function is continuous on the
closed square while taking the prescribed boundary values, because the value at the
corner `(1,0)` would have to be both `0` and `100`. -/
theorem brown_7b_not_exists :
    ¬ ∃ u : (ℝ × ℝ) → ℝ,
      ContinuousOn u (closure Ω) ∧
      (∀ p ∈ interior Ω, True) ∧
      (∀ p ∈ left ∩ Ω,   u p = 0) ∧
      (∀ p ∈ bottom ∩ Ω, u p = 0) ∧
      (∀ p ∈ right ∩ Ω,  u p = 100) ∧
      (∀ p ∈ top ∩ Ω,    u p = 100) ∧
      u (1/2, 1/2) = 25 := by
  rintro ⟨u, hc, -, -, hb, hr, -, -⟩
  have hmem : ((1:ℝ), (0:ℝ)) ∈ Ω := ⟨by norm_num, by norm_num⟩
  have h1 : u (1, 0) = 100 := hr _ ⟨⟨rfl, by norm_num⟩, hmem⟩
  have hsub : bottom ∩ Ω ⊆ closure Ω := by
    rw [closure_Omega]; exact Set.inter_subset_right
  have hcw : ContinuousWithinAt u (bottom ∩ Ω) ((1:ℝ), (0:ℝ)) :=
    (hc _ (by rw [closure_Omega]; exact hmem)).mono hsub
  have himg : u '' (bottom ∩ Ω) ⊆ {0} := by
    rintro _ ⟨p, hp, rfl⟩; exact hb p hp
  have hmemcl := hcw.mem_closure_image corner_mem_closure_bottom
  have h0 : u (1, 0) = 0 := by
    have : u ((1:ℝ), (0:ℝ)) ∈ closure ({0} : Set ℝ) := closure_mono himg hmemcl
    simpa using this
  rw [h1] at h0
  norm_num at h0

/-! ## A corrected formulation -/

/-- The four corners of the plate, where the boundary data is discontinuous. -/
def corners : Set (ℝ × ℝ) := {((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ)), ((0:ℝ), (1:ℝ)), ((1:ℝ), (1:ℝ))}

def edgeLeft : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1}
def edgeRight : Set (ℝ × ℝ) := {p | p.1 = 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1}
def edgeBottom : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}
def edgeTop : Set (ℝ × ℝ) := {p | p.2 = 1 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1}

/-- `u` is a steady temperature distribution on the plate: continuous on the square away
from the four corners, harmonic inside, equal to `0` on the left and bottom edges and to
`100` on the right and top edges. -/
def SteadyTemp (u : ℝ × ℝ → ℝ) : Prop :=
  ContinuousOn u (Ω \ corners) ∧
  HarmonicOn u (interior Ω) ∧
  (∀ p ∈ edgeLeft, u p = 0) ∧
  (∀ p ∈ edgeBottom, u p = 0) ∧
  (∀ p ∈ edgeRight, u p = 100) ∧
  (∀ p ∈ edgeTop, u p = 100)

theorem interior_Omega : interior Ω = Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
  rw [Ω, interior_prod_eq, interior_Icc]

/-- If a ball of radius `r` around `p` fits inside the open square, then `p` is at
distance at least `r` from each of the four sides. -/
theorem ball_subset_interior_bounds {p : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball p r ⊆ interior Ω) :
    r ≤ p.1 ∧ p.1 + r ≤ 1 ∧ r ≤ p.2 ∧ p.2 + r ≤ 1 := by
  rw [interior_Omega] at hsub
  have h1 : Metric.ball p.1 r ⊆ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    have hmem : (x, p.2) ∈ Metric.ball p r := by
      rw [← Prod.mk.eta (p := p), ← ball_prod_same]
      exact ⟨hx, Metric.mem_ball_self hr⟩
    exact (hsub hmem).1
  have h2 : Metric.ball p.2 r ⊆ Set.Ioo (0:ℝ) 1 := by
    intro y hy
    have hmem : (p.1, y) ∈ Metric.ball p r := by
      rw [← Prod.mk.eta (p := p), ← ball_prod_same]
      exact ⟨Metric.mem_ball_self hr, hy⟩
    exact (hsub hmem).2
  rw [Real.ball_eq_Ioo] at h1 h2
  have k1 := (Set.Ioo_subset_Ioo_iff (by linarith : p.1 - r < p.1 + r)).1 h1
  have k2 := (Set.Ioo_subset_Ioo_iff (by linarith : p.2 - r < p.2 + r)).1 h2
  exact ⟨by linarith [k1.1], k1.2, by linarith [k2.1], k2.2⟩

/-- Conversely, distance at least `r` from each side guarantees the ball fits inside. -/
theorem bounds_ball_subset {p : ℝ × ℝ} {r : ℝ} (h1 : r ≤ p.1) (h2 : p.1 + r ≤ 1)
    (h3 : r ≤ p.2) (h4 : p.2 + r ≤ 1) : Metric.ball p r ⊆ interior Ω := by
  rw [interior_Omega]
  intro q hq
  rw [← Prod.mk.eta (p := q), ← Prod.mk.eta (p := p), ← ball_prod_same] at hq
  obtain ⟨hq1, hq2⟩ := hq
  rw [Real.ball_eq_Ioo] at hq1 hq2
  exact ⟨⟨by linarith [hq1.1], by linarith [hq1.2]⟩, ⟨by linarith [hq2.1], by linarith [hq2.2]⟩⟩

/-- Points of the circle of radius `r` around an interior point `p` with
`Metric.ball p r ⊆ interior Ω` lie in the square and avoid the corners. -/
theorem circle_mem_Omega_diff_corners {p : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball p r ⊆ interior Ω) (θ : ℝ) :
    (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ) ∈ Ω \ corners := by
  obtain ⟨b1, b2, b3, b4⟩ := ball_subset_interior_bounds hr hsub
  have hc1 := Real.neg_one_le_cos θ
  have hc2 := Real.cos_le_one θ
  have hs1 := Real.neg_one_le_sin θ
  have hs2 := Real.sin_le_one θ
  have hpyth := Real.sin_sq_add_cos_sq θ
  constructor
  · constructor
    · constructor <;> simp <;> nlinarith
    · constructor <;> simp <;> nlinarith
  · intro hmem
    simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> nlinarith [hpyth]

/-- The integrand defining the circle average is continuous. -/
theorem continuous_circle_restrict {u : ℝ × ℝ → ℝ} (hu : ContinuousOn u (Ω \ corners))
    {p : ℝ × ℝ} {r : ℝ} (hr : 0 < r) (hsub : Metric.ball p r ⊆ interior Ω) :
    Continuous (fun θ : ℝ => u (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ)) :=
  hu.comp_continuous (by fun_prop) (fun θ => circle_mem_Omega_diff_corners hr hsub θ)

/-- Shifting a `2π`-periodic function by `π` does not change its integral over a period. -/
theorem integral_shift_pi {f : ℝ → ℝ} (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (0)..(2 * Real.pi), f (θ + Real.pi) = ∫ θ in (0)..(2 * Real.pi), f θ := by
  rw [intervalIntegral.integral_comp_add_right f Real.pi]
  have h := hf.intervalIntegral_add_eq Real.pi 0
  rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring]
  simpa using h

/-- The rotation by `π` about the centre of the plate exchanges the two `0`-edges with
the two `100`-edges, so it turns a steady temperature `u` into the steady temperature
`p ↦ 100 - u (1 - p.1, 1 - p.2)`. -/
theorem steadyTemp_symm {u : ℝ × ℝ → ℝ} (hu : SteadyTemp u) :
    SteadyTemp (fun p => 100 - u (1 - p.1, 1 - p.2)) := by
  obtain ⟨hcont, hharm, hL, hB, hR, hT⟩ := hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((1 - p.1, 1 - p.2) : ℝ × ℝ)) (Ω \ corners)
        (Ω \ corners) := by
      rintro p ⟨⟨hp1, hp2⟩, hpc⟩
      simp only [Set.mem_Icc] at hp1 hp2
      refine ⟨⟨by constructor <;> simp <;> linarith [hp1.1, hp1.2],
        by constructor <;> simp <;> linarith [hp2.1, hp2.2]⟩, ?_⟩
      intro hmem
      apply hpc
      simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.ext_iff] at hmem ⊢
      rcases hmem with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Or.inl ⟨by linarith, by linarith⟩
    exact continuousOn_const.sub (hcont.comp (by fun_prop) hmaps)
  · -- harmonicity
    intro p hp r hr hball
    obtain ⟨b1, b2, b3, b4⟩ := ball_subset_interior_bounds hr hball
    set q : ℝ × ℝ := (1 - p.1, 1 - p.2) with hqdef
    have hqball : Metric.ball q r ⊆ interior Ω :=
      bounds_ball_subset (by simp [hqdef]; linarith) (by simp [hqdef]; linarith)
        (by simp [hqdef]; linarith) (by simp [hqdef]; linarith)
    have hqmem : q ∈ interior Ω := hqball (Metric.mem_ball_self hr)
    have hmean := hharm q hqmem r hr hqball
    set g : ℝ → ℝ := fun θ => u (q.1 + r * Real.cos θ, q.2 + r * Real.sin θ) with hgdef
    have hgc : Continuous g := continuous_circle_restrict hcont hr hqball
    have hgper : Function.Periodic g (2 * Real.pi) := by
      intro θ
      simp [hgdef, Real.cos_add_two_pi, Real.sin_add_two_pi]
    have hrew : ∀ θ : ℝ,
        (100 : ℝ) - u (1 - (p.1 + r * Real.cos θ), 1 - (p.2 + r * Real.sin θ))
          = 100 - g (θ + Real.pi) := by
      intro θ
      have : ((1 - (p.1 + r * Real.cos θ), 1 - (p.2 + r * Real.sin θ)) : ℝ × ℝ)
          = (q.1 + r * Real.cos (θ + Real.pi), q.2 + r * Real.sin (θ + Real.pi)) := by
        rw [Real.cos_add_pi, Real.sin_add_pi]
        simp [hqdef]
        constructor <;> ring
      rw [this]
    have hint : ∫ θ in (0)..(2 * Real.pi),
        ((100 : ℝ) - u (1 - (p.1 + r * Real.cos θ), 1 - (p.2 + r * Real.sin θ)))
        = 100 * (2 * Real.pi) - ∫ θ in (0)..(2 * Real.pi), g θ := by
      have hshift : Continuous fun θ : ℝ => g (θ + Real.pi) := hgc.comp (by fun_prop)
      simp only [hrew]
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hshift.intervalIntegrable _ _), integral_shift_pi hgper]
      simp
      ring
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    show (100 : ℝ) - u q = circleAvg (fun p : ℝ × ℝ => 100 - u (1 - p.1, 1 - p.2)) p r
    rw [circleAvg]
    simp only []
    rw [hint]
    have hmean' : u q = (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), g θ := hmean
    have : ∫ θ in (0)..(2 * Real.pi), g θ = (2 * Real.pi) * u q := by
      rw [hmean']; field_simp
    rw [this]
    field_simp
  · -- left edge
    rintro p ⟨hp1, hp2⟩
    have : ((1 - p.1, 1 - p.2) : ℝ × ℝ) ∈ edgeRight := by
      refine ⟨by simp [hp1], ?_⟩
      simp only [Set.mem_Ioo] at hp2 ⊢
      constructor <;> linarith [hp2.1, hp2.2]
    simp [hR _ this]
  · -- bottom edge
    rintro p ⟨hp2, hp1⟩
    have : ((1 - p.1, 1 - p.2) : ℝ × ℝ) ∈ edgeTop := by
      refine ⟨by simp [hp2], ?_⟩
      simp only [Set.mem_Ioo] at hp1 ⊢
      constructor <;> linarith [hp1.1, hp1.2]
    simp [hT _ this]
  · -- right edge
    rintro p ⟨hp1, hp2⟩
    have : ((1 - p.1, 1 - p.2) : ℝ × ℝ) ∈ edgeLeft := by
      refine ⟨by simp [hp1], ?_⟩
      simp only [Set.mem_Ioo] at hp2 ⊢
      constructor <;> linarith [hp2.1, hp2.2]
    simp [hL _ this]
  · -- top edge
    rintro p ⟨hp2, hp1⟩
    have : ((1 - p.1, 1 - p.2) : ℝ × ℝ) ∈ edgeBottom := by
      refine ⟨by simp [hp2], ?_⟩
      simp only [Set.mem_Ioo] at hp1 ⊢
      constructor <;> linarith [hp1.1, hp1.2]
    simp [hB _ this]

/-- **The steady temperature at the centre of the plate is `50`, not `25`.**
If `u` is a steady temperature distribution and the problem has a unique solution, then
`u (1/2, 1/2) = 50`. -/
theorem steadyTemp_center_eq_fifty {u : ℝ × ℝ → ℝ} (hu : SteadyTemp u)
    (huniq : ∀ v : ℝ × ℝ → ℝ, SteadyTemp v → v = u) :
    u (1/2, 1/2) = 50 := by
  have hv := huniq _ (steadyTemp_symm hu)
  have := congrFun hv ((1/2 : ℝ), (1/2 : ℝ))
  norm_num at this
  linarith

/-! ## The vacuous harmonicity clause determines nothing -/

theorem denom_pos {p : ℝ × ℝ} (hp : p ∈ Ω \ corners) :
    0 < p.1 * p.2 + 3 * (1 - p.1) * (1 - p.2) := by
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hc⟩ := hp
  rcases lt_or_eq_of_le (mul_nonneg h1 h3 : (0:ℝ) ≤ p.1 * p.2) with h | h
  · nlinarith
  · rcases lt_or_eq_of_le (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p.1)
      (by linarith : (0:ℝ) ≤ 1 - p.2)) with h' | h'
    · nlinarith
    · exfalso
      apply hc
      rcases mul_eq_zero.1 h.symm with hx | hy
      · rcases mul_eq_zero.1 h'.symm with hx1 | hy1
        · exact absurd (by linarith : (0:ℝ) = 1) (by norm_num)
        · exact Or.inr (Or.inr (Or.inl (by simp [Prod.ext_iff]; constructor <;> linarith)))
      · rcases mul_eq_zero.1 h'.symm with hx1 | hy1
        · exact Or.inr (Or.inl (by simp [Prod.ext_iff]; constructor <;> linarith))
        · exact absurd (by linarith : (0:ℝ) = 1) (by norm_num)

/-- With the harmonicity clause left vacuous, the value at the centre is not determined at
all by the boundary data: here is a continuous (but of course non-harmonic) function on the
square minus its corners with the prescribed boundary values and value `25` at the centre.
So the proposed statement, once its corner inconsistency is repaired, says nothing about
the physics of the problem. -/
theorem exists_boundary_data_center_25 :
    ∃ u : ℝ × ℝ → ℝ,
      ContinuousOn u (Ω \ corners) ∧
      (∀ p ∈ edgeLeft, u p = 0) ∧ (∀ p ∈ edgeBottom, u p = 0) ∧
      (∀ p ∈ edgeRight, u p = 100) ∧ (∀ p ∈ edgeTop, u p = 100) ∧
      u (1/2, 1/2) = 25 := by
  refine ⟨fun p => 100 * (p.1 * p.2) / (p.1 * p.2 + 3 * (1 - p.1) * (1 - p.2)),
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun p hp => ne_of_gt (denom_pos hp)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨hp1, -⟩
    simp only [hp1]
    norm_num
  · rintro p ⟨hp2, -⟩
    simp only [hp2]
    norm_num
  · rintro p ⟨hp1, hp2⟩
    simp only [hp1]
    rw [show (1:ℝ) * p.2 + 3 * (1 - 1) * (1 - p.2) = p.2 by ring,
      show (100:ℝ) * ((1:ℝ) * p.2) = 100 * p.2 by ring, mul_div_assoc,
      div_self (ne_of_gt hp2.1), mul_one]
  · rintro p ⟨hp2, hp1⟩
    simp only [hp2]
    rw [show p.1 * (1:ℝ) + 3 * (1 - p.1) * (1 - 1) = p.1 by ring,
      show (100:ℝ) * (p.1 * (1:ℝ)) = 100 * p.1 by ring, mul_div_assoc,
      div_self (ne_of_gt hp1.1), mul_one]
  · norm_num
