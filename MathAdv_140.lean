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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Filter Topology
open scoped BoundedContinuousFunction

/-!
# Basis projections of a Banach space are bounded, uniformly

Let `(xₙ)` be a (Schauder) basis of a Banach space `X`, i.e. every `v ∈ X` has a *unique*
expansion `v = ∑ᵢ λᵢ xᵢ`. The partial sum operators `Pₙ v = ∑_{i ≤ n} λᵢ xᵢ` are then bounded
operators with `sup_n ‖Pₙ‖ < ∞`.

The formal statement `bollobas_5_20` below is the version of this fact with the *uniqueness*
part of the definition of a basis included as a hypothesis (`repr_unique`); the theorem
`bollobas_5_20_without_uniqueness_false` at the end of the file shows that the uniqueness
hypothesis cannot be omitted.

The textbook argument derives boundedness of each `Pₙ` from a completeness argument and then
concludes `sup_n ‖Pₙ‖ < ∞` from the uniform boundedness principle. The proof formalised here
takes a slightly different route with the same ingredients: the map `Phi : v ↦ (Pₙ v)ₙ`
into the Banach space of bounded `X`-valued sequences is shown to have a closed graph, and
the closed graph theorem then yields boundedness of all `Pₙ` by the single constant `‖Phi‖`.
-/

namespace Bollobas520

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `n`-th partial sum `∑_{i ≤ n} (repr v i) • x i` of the expansion of `v`. -/
noncomputable def partialSum (x : ℕ → X) (repr : X → ℕ → ℝ) (v : X) (n : ℕ) : X :=
  ∑ i ∈ Finset.range (n + 1), repr v i • x i

lemma tendsto_partialSum {x : ℕ → X} {repr : X → ℕ → ℝ}
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v) (v : X) :
    Tendsto (partialSum x repr v) atTop (𝓝 v) :=
  ((hsum v).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

lemma exists_dist_bound {x : ℕ → X} {repr : X → ℕ → ℝ}
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v) (v : X) :
    ∃ C : ℝ, ∀ m n : ℕ, dist (partialSum x repr v m) (partialSum x repr v n) ≤ C := by
  obtain ⟨R, _, hR⟩ := cauchySeq_bdd (tendsto_partialSum hsum v).cauchySeq
  exact ⟨R, fun m n => (hR m n).le⟩

/-- The linear map sending `v` to the bounded sequence of its partial sums. -/
noncomputable def Phi (x : ℕ → X) (repr : X → ℕ → ℝ)
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v)
    (hlin : ∀ i, IsLinearMap ℝ (fun v : X => repr v i)) : X →ₗ[ℝ] (ℕ →ᵇ X) where
  toFun v := BoundedContinuousFunction.mkOfDiscrete (partialSum x repr v)
      (exists_dist_bound hsum v).choose (exists_dist_bound hsum v).choose_spec
  map_add' v w := by
    ext n
    simp only [BoundedContinuousFunction.mkOfDiscrete, partialSum,
      BoundedContinuousFunction.coe_add, Pi.add_apply, BoundedContinuousFunction.coe_mk]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [(hlin i).map_add, add_smul]
  map_smul' c v := by
    ext n
    simp only [BoundedContinuousFunction.mkOfDiscrete, partialSum, RingHom.id_apply,
      BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mk, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hlin i).map_smul, smul_smul, smul_eq_mul]

@[simp] lemma Phi_apply {x : ℕ → X} {repr : X → ℕ → ℝ}
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v)
    (hlin : ∀ i, IsLinearMap ℝ (fun v : X => repr v i)) (v : X) (n : ℕ) :
    Phi x repr hsum hlin v n = partialSum x repr v n := rfl

/-- A limit of scalar multiples of `y` is again a scalar multiple of `y`. -/
lemma exists_smul_of_tendsto {y : X} {c : ℕ → ℝ} {w : X}
    (h : Tendsto (fun k => c k • y) atTop (𝓝 w)) : ∃ t : ℝ, w = t • y := by
  have hmem : w ∈ closure ((Submodule.span ℝ {y} : Submodule ℝ X) : Set X) :=
    mem_closure_of_tendsto h (Eventually.of_forall fun _ =>
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  rw [(Submodule.span ℝ {y}).closed_of_finiteDimensional.closure_eq] at hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨t, ht.symm⟩

/-- If the partial sums of `Phi (u k)` converge uniformly to `g` and `u k → v`,
then `g n → v` as `n → ∞`. -/
lemma tendsto_of_uniform {x : ℕ → X} {repr : X → ℕ → ℝ}
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v)
    (hlin : ∀ i, IsLinearMap ℝ (fun v : X => repr v i))
    {u : ℕ → X} {v : X} {g : ℕ →ᵇ X}
    (hu : Tendsto u atTop (𝓝 v))
    (hg : Tendsto (fun k => Phi x repr hsum hlin (u k)) atTop (𝓝 g)) :
    Tendsto (fun n => g n) atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hg (ε / 3) hε3
  obtain ⟨K₂, hK₂⟩ := Metric.tendsto_atTop.mp hu (ε / 3) hε3
  set k := max K₁ K₂
  have hk₁ : dist (Phi x repr hsum hlin (u k)) g < ε / 3 := hK₁ k (le_max_left _ _)
  have hk₂ : dist (u k) v < ε / 3 := hK₂ k (le_max_right _ _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_partialSum hsum (u k)) (ε / 3) hε3
  refine ⟨N, fun n hn => ?_⟩
  have e1 : dist (g n) (partialSum x repr (u k) n) < ε / 3 := by
    have h' : dist (Phi x repr hsum hlin (u k) n) (g n)
        ≤ dist (Phi x repr hsum hlin (u k)) g :=
      BoundedContinuousFunction.dist_coe_le_dist n
    rw [dist_comm]
    calc dist (partialSum x repr (u k) n) (g n)
        = dist (Phi x repr hsum hlin (u k) n) (g n) := rfl
      _ ≤ dist (Phi x repr hsum hlin (u k)) g := h'
      _ < ε / 3 := hk₁
  have e2 : dist (partialSum x repr (u k) n) (u k) < ε / 3 := hN n hn
  calc dist (g n) v
      ≤ dist (g n) (partialSum x repr (u k) n) + dist (partialSum x repr (u k) n) (u k)
          + dist (u k) v := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

section Complete

variable [CompleteSpace X]

/-- `Phi` has closed graph, hence is continuous. -/
theorem Phi_continuous {x : ℕ → X} {repr : X → ℕ → ℝ}
    (hsum : ∀ v : X, HasSum (fun i => repr v i • x i) v)
    (hlin : ∀ i, IsLinearMap ℝ (fun v : X => repr v i))
    (huniq : ∀ (a : ℕ → ℝ) (v : X),
      Tendsto (fun n => ∑ i ∈ Finset.range n, a i • x i) atTop (𝓝 v) → ∀ i, a i = repr v i) :
    Continuous (Phi x repr hsum hlin) := by
  refine (Phi x repr hsum hlin).continuous_of_seq_closed_graph ?_
  intro u v g hu hg
  have hg' : Tendsto (fun k => Phi x repr hsum hlin (u k)) atTop (𝓝 g) := hg
  have hev : ∀ n : ℕ, Tendsto (fun k => partialSum x repr (u k) n) atTop (𝓝 (g n)) := by
    intro n
    have h := ((BoundedContinuousFunction.evalCLM ℝ n).continuous.tendsto g).comp hg'
    simpa [Function.comp_def] using h
  obtain ⟨a₀, ha₀⟩ : ∃ t : ℝ, g 0 = t • x 0 :=
    exists_smul_of_tendsto (c := fun k => repr (u k) 0) (by simpa [partialSum] using hev 0)
  have hb : ∀ j : ℕ, ∃ t : ℝ, g (j + 1) - g j = t • x (j + 1) := by
    intro j
    refine exists_smul_of_tendsto (c := fun k => repr (u k) (j + 1)) ?_
    have h := (hev (j + 1)).sub (hev j)
    simpa [partialSum, Finset.sum_range_succ] using h
  choose b hbspec using hb
  set a : ℕ → ℝ := fun i => match i with | 0 => a₀ | (j + 1) => b j with ha
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), a i • x i = g n := by
    intro n
    induction n with
    | zero => simpa [ha] using ha₀.symm
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have : a (m + 1) • x (m + 1) = g (m + 1) - g m := (hbspec m).symm
        rw [this]
        abel
  have hgv : Tendsto (fun n => g n) atTop (𝓝 v) := tendsto_of_uniform hsum hlin hu hg'
  have hps : Tendsto (fun n => ∑ i ∈ Finset.range n, a i • x i) atTop (𝓝 v) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [htel] using hgv
  have hcoef := huniq a v hps
  ext n
  rw [Phi_apply, partialSum, ← htel n]
  exact Finset.sum_congr rfl fun i _ => by rw [hcoef i]

end Complete

end Bollobas520

/-- **Basis projections are bounded, uniformly.**
Let `(xᵢ)` be a basis of the Banach space `X`: every `v ∈ X` is the sum of the series
`∑ᵢ (repr v i) • xᵢ` (`repr_sum`), the coefficients depend linearly on `v` (`repr_linear`),
and the expansion is unique in the sense that any sequence of coefficients whose partial sums
converge to `v` must be the sequence `repr v` (`repr_unique`). Then the partial sum
projections `Pₙ` are bounded linear operators, and their norms are uniformly bounded. -/
theorem bollobas_5_20
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (x : ℕ → X)
    (repr : X → ℕ → ℝ)
    (repr_sum : ∀ v : X, HasSum (fun i ↦ repr v i • x i) v)
    (repr_linear : ∀ i, IsLinearMap ℝ (fun v : X => repr v i))
    (repr_unique : ∀ (a : ℕ → ℝ) (v : X),
      Tendsto (fun n => ∑ i ∈ Finset.range n, a i • x i) atTop (𝓝 v) → ∀ i, a i = repr v i) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ P : ℕ → X →L[ℝ] X,
        (∀ n v, P n v = ∑ i ∈ Finset.range (n + 1), repr v i • x i) ∧
        ∀ n, ‖P n‖ ≤ C := by
  have hcont := Bollobas520.Phi_continuous repr_sum repr_linear repr_unique
  set Φ : X →L[ℝ] (ℕ →ᵇ X) := ⟨Bollobas520.Phi x repr repr_sum repr_linear, hcont⟩
  refine ⟨‖Φ‖, norm_nonneg _, fun n => (BoundedContinuousFunction.evalCLM ℝ n).comp Φ, ?_, ?_⟩
  · intro n v; rfl
  · intro n
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    calc ‖((BoundedContinuousFunction.evalCLM ℝ n).comp Φ) v‖ = ‖Φ v n‖ := rfl
      _ ≤ ‖Φ v‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖Φ‖ * ‖v‖ := Φ.le_opNorm v

/-!
## The uniqueness hypothesis cannot be dropped

We now show formally that the statement obtained from `bollobas_5_20` by deleting the
uniqueness hypothesis `repr_unique` is false.
-/

namespace Bollobas520

/-- `ℓ²` of real sequences. -/
abbrev EllTwo := lp (fun _ : ℕ => ℝ) 2

/-- The `n`-th standard unit vector of `ℓ²`. -/
noncomputable def es (n : ℕ) : EllTwo := lp.single 2 n (1 : ℝ)

lemma smul_es (i : ℕ) (c : ℝ) : c • es i = lp.single 2 i c := by
  ext j
  simp [es, lp.single_apply, Pi.single_apply, lp.coeFn_smul]

lemma norm_es (n : ℕ) : ‖es n‖ = 1 := by
  simp [es, lp.norm_single]

lemma hasSum_es (v : EllTwo) : HasSum (fun i => (v i) • es i) v := by
  have h := lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) v
  simpa [smul_es] using h

lemma linearIndependent_es : LinearIndependent ℝ es := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have h := congrFun (congrArg (fun w : EllTwo => (w : ℕ → ℝ)) hs) i
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, es,
    lp.single_apply, Pi.single_apply, lp.coeFn_zero, Pi.zero_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro j _ hj
    have : (if i = j then (1 : ℝ) else 0) = 0 := by
      simp [hj.symm]
    rw [this, mul_zero]
  · intro h'; exact absurd hi h'

/-- On a vector space containing a linearly independent sequence there is a linear functional
taking the value `n` at the `n`-th member of the sequence. -/
lemma exists_unbounded_functional {X : Type*} [AddCommGroup X] [Module ℝ X]
    {e : ℕ → X} (hind : LinearIndependent ℝ e) :
    ∃ f : X →ₗ[ℝ] ℝ, ∀ n : ℕ, f (e n) = (n : ℝ) := by
  set f₀ : (Submodule.span ℝ (Set.range e)) →ₗ[ℝ] ℝ :=
    (Finsupp.linearCombination ℝ (fun n : ℕ => (n : ℝ))).comp hind.repr with hf₀
  obtain ⟨g, hg⟩ := f₀.exists_extend
  refine ⟨g, fun n => ?_⟩
  have hmem : e n ∈ Submodule.span ℝ (Set.range e) :=
    Submodule.subset_span (Set.mem_range_self n)
  have hgn := LinearMap.congr_fun hg ⟨e n, hmem⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at hgn
  rw [show g (e n) = g ((⟨e n, hmem⟩ : Submodule.span ℝ (Set.range e)) : X) from rfl, hgn, hf₀]
  simp [hind.repr_eq_single n ⟨e n, hmem⟩ rfl]

/-- The system of vectors used for the counterexample. -/
noncomputable def ceX (n : ℕ) : EllTwo :=
  match n with
  | 0 => es 0
  | 1 => -es 0
  | (k + 2) => es (k + 1)

/-- The coefficients used for the counterexample; `f` is an arbitrary linear functional. -/
noncomputable def ceRepr (f : EllTwo →ₗ[ℝ] ℝ) (v : EllTwo) (n : ℕ) : ℝ :=
  match n with
  | 0 => f v
  | 1 => f v - v 0
  | (k + 2) => v (k + 1)

lemma coord_isLinearMap (j : ℕ) : IsLinearMap ℝ (fun v : EllTwo => v j) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

lemma ceRepr_isLinearMap (f : EllTwo →ₗ[ℝ] ℝ) (i : ℕ) :
    IsLinearMap ℝ (fun v : EllTwo => ceRepr f v i) := by
  match i with
  | 0 => exact ⟨fun v w => f.map_add v w, fun c v => f.map_smul c v⟩
  | 1 =>
      exact ⟨fun v w => by
              simp only [ceRepr, f.map_add, (coord_isLinearMap 0).map_add]; ring,
             fun c v => by
              simp only [ceRepr, f.map_smul, (coord_isLinearMap 0).map_smul, smul_eq_mul]
              ring⟩
  | (_k + 2) => exact coord_isLinearMap (_ + 1)

lemma ceRepr_hasSum (f : EllTwo →ₗ[ℝ] ℝ) (v : EllTwo) :
    HasSum (fun i => ceRepr f v i • ceX i) v := by
  have base := hasSum_es v
  have h1 : HasSum (fun n => (v (n + 1)) • es (n + 1)) (v - (v 0) • es 0) :=
    (hasSum_nat_add_iff (f := fun i => (v i) • es i) 1).mpr (by simpa using base)
  have h2 : HasSum (fun n => ceRepr f v (n + 2) • ceX (n + 2)) (v - (v 0) • es 0) := h1
  have h3 := (hasSum_nat_add_iff (f := fun i => ceRepr f v i • ceX i) 2).mp h2
  have hsum2 : ∑ i ∈ Finset.range 2, ceRepr f v i • ceX i = (v 0) • es 0 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      ceRepr, ceX]
    module
  rw [hsum2] at h3
  simpa using h3

end Bollobas520

/-- **The uniqueness hypothesis is necessary.** Without the requirement that the expansion of
a vector in the system `(xᵢ)` be unique, the conclusion of `bollobas_5_20` fails. -/
theorem bollobas_5_20_without_uniqueness_false :
    ¬ ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        (x : ℕ → X) (repr : X → ℕ → ℝ),
        (∀ v : X, HasSum (fun i ↦ repr v i • x i) v) →
        (∀ i, IsLinearMap ℝ (fun v : X => repr v i)) →
        ∃ C : ℝ, 0 ≤ C ∧
          ∃ P : ℕ → X →L[ℝ] X,
            (∀ n v, P n v = ∑ i ∈ Finset.range (n + 1), repr v i • x i) ∧
            ∀ n, ‖P n‖ ≤ C := by
  intro h
  obtain ⟨f, hf⟩ := Bollobas520.exists_unbounded_functional Bollobas520.linearIndependent_es
  obtain ⟨C, _, P, hP, hPC⟩ :=
    h Bollobas520.EllTwo Bollobas520.ceX (Bollobas520.ceRepr f)
      (Bollobas520.ceRepr_hasSum f) (Bollobas520.ceRepr_isLinearMap f)
  have key : ∀ v : Bollobas520.EllTwo, |f v| ≤ C * ‖v‖ := by
    intro v
    have h0 : P 0 v = f v • Bollobas520.es 0 := by
      rw [hP 0 v]
      simp [Bollobas520.ceRepr, Bollobas520.ceX]
    have : ‖P 0 v‖ ≤ C * ‖v‖ :=
      le_trans ((P 0).le_opNorm v) (by gcongr; exact hPC 0)
    rw [h0, norm_smul, Bollobas520.norm_es] at this
    simpa using this
  obtain ⟨n, _hn⟩ := exists_nat_gt C
  have := key (Bollobas520.es n)
  rw [hf n, Bollobas520.norm_es, mul_one, abs_of_nonneg (Nat.cast_nonneg n)] at this
  linarith
