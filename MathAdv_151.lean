import Mathlib

open scoped Real
open Topology

/-!
# Pressley 4.1.4 : the cylinder is a single surface patch, the sphere is not

A *surface patch* is a homeomorphism from an open subset `U ⊆ ℝ²` onto its image
in `ℝ³` (this is the topological content of the notion of a regular surface patch:
`X : U → ℝ³` is required to be a homeomorphism onto its image).

We show:
* the unit cylinder `x² + y² = 1` is the image of a single patch, namely
  `(x, y) ↦ (x/r, y/r, log r)` defined on the punctured plane `ℝ² \ {0}`;
* the unit sphere is **not** the image of a single patch: it is compact, so a
  patch covering it would make its (open) domain `U ⊆ ℝ²` compact, hence clopen,
  hence all of `ℝ²`, contradicting the noncompactness of the plane.
-/

/-- The unit cylinder `{(x, y, z) : x² + y² = 1}` in `ℝ³`. -/
def unitCylinder : Set (ℝ × ℝ × ℝ) :=
  { p | p.1 ^ 2 + p.2.1 ^ 2 = (1 : ℝ) }

/-- The unit sphere in `ℝ³` (as a metric sphere around the origin). -/
def unitSphere : Set (ℝ × ℝ × ℝ) :=
  Metric.sphere (0 : ℝ × ℝ × ℝ) 1

/-- `S ⊆ ℝ³` is covered by a single surface patch: there is an open set `U ⊆ ℝ²`
and a homeomorphism (a topological embedding) `X : U → ℝ³` whose image is `S`. -/
def IsSinglePatch (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ∃ X : U → ℝ × ℝ × ℝ,
    IsEmbedding X ∧ Set.range X = S

namespace Pressley414

/-- The domain of the cylinder patch: the punctured plane. -/
def U : Set (ℝ × ℝ) := {p | p ≠ 0}

lemma isOpen_U : IsOpen U := isOpen_compl_singleton

lemma radius_pos {p : ℝ × ℝ} (hp : p ∈ U) : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
  have h : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
    intro h
    have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have h2 : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    exact hp (Prod.ext h1 h2)
  have : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  exact Real.sqrt_pos.mpr (lt_of_le_of_ne this (Ne.symm h))

/-- The cylinder patch `(x, y) ↦ (x/r, y/r, log r)` with `r = √(x²+y²)`. -/
noncomputable def cylPatch : U → ℝ × ℝ × ℝ := fun p =>
  (p.1.1 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2),
   p.1.2 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2),
   Real.log (Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2)))

/-- A continuous left inverse (on the cylinder) of the patch. -/
noncomputable def cylInv : ℝ × ℝ × ℝ → ℝ × ℝ := fun q =>
  (q.1 * Real.exp q.2.2, q.2.1 * Real.exp q.2.2)

lemma continuous_cylInv : Continuous cylInv := by
  unfold cylInv
  fun_prop

lemma continuous_cylPatch : Continuous cylPatch := by
  have hne : ∀ p : U, Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) ≠ 0 := fun p =>
    ne_of_gt (radius_pos p.2)
  unfold cylPatch
  have hc : Continuous fun p : U => Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) := by fun_prop
  exact (Continuous.div (by fun_prop) hc hne).prodMk
    ((Continuous.div (by fun_prop) hc hne).prodMk (hc.log hne))

lemma cylInv_comp : cylInv ∘ cylPatch = Subtype.val := by
  funext p
  have hr : 0 < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) := radius_pos p.2
  have hexp : Real.exp (Real.log (Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2)))
      = Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) := Real.exp_log hr
  simp only [Function.comp_apply, cylInv, cylPatch, hexp]
  refine Prod.ext ?_ ?_ <;> simp [ne_of_gt hr]

lemma isEmbedding_cylPatch : IsEmbedding cylPatch := by
  refine IsEmbedding.of_comp continuous_cylPatch continuous_cylInv ?_
  rw [cylInv_comp]
  exact IsEmbedding.subtypeVal

lemma range_cylPatch : Set.range cylPatch = unitCylinder := by
  apply Set.eq_of_subset_of_subset
  · rintro q ⟨p, rfl⟩
    have hr : 0 < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) := radius_pos p.2
    have hsq : Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2) ^ 2 = p.1.1 ^ 2 + p.1.2 ^ 2 :=
      Real.sq_sqrt (by positivity)
    show (p.1.1 / _) ^ 2 + (p.1.2 / _) ^ 2 = (1 : ℝ)
    field_simp [div_pow]
    linarith [hsq]
  · rintro ⟨a, b, c⟩ h
    have hab : a ^ 2 + b ^ 2 = 1 := h
    have hexp : (0 : ℝ) < Real.exp c := Real.exp_pos c
    have hmem : (a * Real.exp c, b * Real.exp c) ∈ U := by
      intro hz
      have h1 : a * Real.exp c = 0 := congrArg Prod.fst hz
      have h2 : b * Real.exp c = 0 := congrArg Prod.snd hz
      have ha : a = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h (ne_of_gt hexp)
      have hb : b = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (ne_of_gt hexp)
      rw [ha, hb] at hab; norm_num at hab
    refine ⟨⟨(a * Real.exp c, b * Real.exp c), hmem⟩, ?_⟩
    have hr : Real.sqrt ((a * Real.exp c) ^ 2 + (b * Real.exp c) ^ 2) = Real.exp c := by
      have : (a * Real.exp c) ^ 2 + (b * Real.exp c) ^ 2 = (Real.exp c) ^ 2 := by
        nlinarith [hab]
      rw [this, Real.sqrt_sq (le_of_lt hexp)]
    simp only [cylPatch, hr, Real.log_exp]
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;>
      simp [ne_of_gt hexp]

theorem isSinglePatch_unitCylinder : IsSinglePatch unitCylinder :=
  ⟨U, isOpen_U, cylPatch, isEmbedding_cylPatch, range_cylPatch⟩

theorem not_isSinglePatch_unitSphere : ¬ IsSinglePatch unitSphere := by
  rintro ⟨V, hV, X, hX, hrange⟩
  -- the sphere is compact, hence so is the domain `V`
  have hcompact_sphere : IsCompact unitSphere := isCompact_sphere _ _
  have hcompactV : IsCompact V := by
    rw [isCompact_iff_compactSpace, ← isCompact_univ_iff, hX.isCompact_iff]
    simpa [hrange] using hcompact_sphere
  -- `V` is nonempty, since the sphere is
  have hne : V.Nonempty := by
    have : unitSphere.Nonempty := by
      refine ⟨(1, 0, 0), ?_⟩
      simp [unitSphere, Prod.norm_def]
    rw [← hrange] at this
    obtain ⟨q, p, rfl⟩ := this
    exact ⟨p.1, p.2⟩
  -- a nonempty compact open subset of the plane must be everything
  have hclopen : IsClopen V := ⟨hcompactV.isClosed, hV⟩
  have hVuniv : V = Set.univ := by
    rcases isClopen_iff.mp hclopen with h | h
    · exact absurd h (Set.nonempty_iff_ne_empty.mp hne)
    · exact h
  rw [hVuniv] at hcompactV
  exact (noncompact_univ (ℝ × ℝ)) hcompactV

end Pressley414

/-- **Pressley 4.1.4.** The unit cylinder is the image of a single surface patch,
while the unit sphere is not. -/
theorem Pressley_4_1_4_param :
    IsSinglePatch unitCylinder ∧ ¬ IsSinglePatch unitSphere :=
  ⟨Pressley414.isSinglePatch_unitCylinder, Pressley414.not_isSinglePatch_unitSphere⟩

/-!
## On the literal statement without a continuity requirement

The following is the statement one gets by asking only for a *function*
`X : U → ℝ³` with `Set.range X = S`, with no continuity/embedding condition:

```
theorem Pressley_4_1_4_param' :
  (∃ (U : Set (ℝ × ℝ)), IsOpen U ∧ ∃ X : (U → (ℝ × ℝ × ℝ)),
      Set.range X = unitCylinder) ∧
  ¬ (∃ (U : Set (ℝ × ℝ)), IsOpen U ∧ ∃ X : (U → (ℝ × ℝ × ℝ)),
      Set.range X = unitSphere)
```

This is **false**: its second conjunct fails, because a bare set-theoretic
surjection from the plane onto the sphere exists (both sets have cardinality
`𝔠`).  This is why the notion of a surface patch is formalized above as a
topological embedding.  The refutation is `exists_surjection_onto_unitSphere`
below.
-/

namespace Pressley414

/-- Without any continuity assumption, the plane does admit a (set-theoretic)
parametrization of the unit sphere; hence the second conjunct of the naive
formalization of Pressley 4.1.4 is false. -/
theorem exists_surjection_onto_unitSphere :
    ∃ (V : Set (ℝ × ℝ)), IsOpen V ∧ ∃ X : (V → (ℝ × ℝ × ℝ)),
      Set.range X = unitSphere := by
  have hcard : Cardinal.mk (ℝ × ℝ × ℝ) ≤ Cardinal.mk (ℝ × ℝ) := by
    simp [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.continuum_mul_self]
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hcard
  have hbase : ((1 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ unitSphere := by
    simp [unitSphere, Prod.norm_def]
  classical
  refine ⟨Set.univ, isOpen_univ, fun p =>
    if h : ∃ q ∈ unitSphere, e q = p.1 then h.choose else (1, 0, 0), ?_⟩
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨p, rfl⟩
    by_cases h : ∃ q ∈ unitSphere, e q = p.1
    · simpa [h] using h.choose_spec.1
    · simpa [h] using hbase
  · intro q hq
    refine ⟨⟨e q, trivial⟩, ?_⟩
    have h : ∃ r ∈ unitSphere, e r = (⟨e q, trivial⟩ : (Set.univ : Set (ℝ × ℝ))).1 :=
      ⟨q, hq, rfl⟩
    have hspec := h.choose_spec.2
    simp only [dif_pos h]
    exact e.injective hspec

end Pressley414
