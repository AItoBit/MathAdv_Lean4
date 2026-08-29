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
# Splitting 12 children into four playgroups, keeping two sibling pairs together

The number of ways to split `12` children into four (nonempty, unlabelled) playgroups
so that two given pairs of siblings are never separated is `34105`, the Stirling number
of the second kind `S(10, 4)`: gluing each sibling pair into a single unit leaves `10` units
to be partitioned into `4` nonempty blocks. (So the relevant concept is (b), Stirling numbers
of the second kind.)

The proof reduces the problem to counting surjections from a 10-element set onto the four
groups (there are `818520 = 24 * 34105` of them) and then divides by `4! = 24`, using that the
relabelling action of `Equiv.Perm (Fin 4)` on surjections is free.
-/

/-- An assignment of the 12 children to 4 (labelled) groups. -/
def Assign := Fin 12 → Fin 4

/-- The two sibling pairs `{s₁, s₂}` and `{t₁, t₂}` are kept together. -/
def SiblingsTogether (s₁ s₂ t₁ t₂ : Fin 12) (f : Assign) : Prop :=
  f s₁ = f s₂ ∧ f t₁ = f t₂

/-- Every one of the four groups is nonempty. -/
def AllGroupsUsed (f : Assign) : Prop := Function.Surjective f

/-- Valid assignments into *labelled* groups. -/
def ValidLabeled (s₁ s₂ t₁ t₂ : Fin 12) : Type :=
  { f : Assign // AllGroupsUsed f ∧ SiblingsTogether s₁ s₂ t₁ t₂ f }

/-- Valid assignments into *unlabelled* groups: labelled ones up to relabelling. -/
def ValidUnlabeledReps (s₁ s₂ t₁ t₂ : Fin 12) : Type := by
  classical
  exact Quot
    (fun f g : ValidLabeled s₁ s₂ t₁ t₂ =>
      ∃ σ : Equiv.Perm (Fin 4), (fun c => σ (f.1 c)) = g.1)

namespace Bona49

/-- The relation of "differing by a relabelling of the four groups". -/
def RelLabeled (s₁ s₂ t₁ t₂ : Fin 12) (f g : ValidLabeled s₁ s₂ t₁ t₂) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), (fun c => σ (f.1 c)) = g.1

/-- Surjections from a 10-element set onto the four groups. -/
def Surj10 : Type := { g : Fin 10 → Fin 4 // Function.Surjective g }

/-- Relabelling relation on `Surj10`. -/
def Rel10 (g h : Surj10) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), (fun c => σ (g.1 c)) = h.1

instance : SMul (Equiv.Perm (Fin 4)) Surj10 :=
  ⟨fun σ g => ⟨fun c => σ (g.1 c), σ.surjective.comp g.2⟩⟩

instance : MulAction (Equiv.Perm (Fin 4)) Surj10 where
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

instance : Fintype Surj10 := by
  unfold Surj10; infer_instance

lemma smul_def (σ : Equiv.Perm (Fin 4)) (g : Surj10) : (σ • g).1 = fun c => σ (g.1 c) := rfl

/-- There are `4! * S(10,4) = 818520` surjections from a 10-element set onto a 4-element set. -/
lemma card_Surj10 : Nat.card Surj10 = 818520 := by
  rw [Nat.card_eq_fintype_card]
  show Fintype.card { g : Fin 10 → Fin 4 // Function.Surjective g } = 818520
  rw [Fintype.card_subtype]
  native_decide

lemma card_G4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

lemma rel10_iff_orbitRel (g h : Surj10) :
    Rel10 g h ↔ (MulAction.orbitRel (Equiv.Perm (Fin 4)) Surj10) g h := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ⁻¹, ?_⟩
    apply Subtype.ext
    rw [smul_def, ← hσ]
    ext c
    simp
  · rintro ⟨σ, hσ⟩
    refine ⟨σ⁻¹, ?_⟩
    rw [← hσ]
    ext c
    simp [smul_def]

/-- The relabelling action on surjections is free, so every orbit has `24` elements. -/
lemma card_orbit (x : Surj10) :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin 4)) x) = 24 := by
  have hbij : Function.Bijective (fun σ : Equiv.Perm (Fin 4) =>
      (⟨σ • x, MulAction.mem_orbit x σ⟩ : MulAction.orbit (Equiv.Perm (Fin 4)) x)) := by
    constructor
    · intro σ τ h
      have h1 : (σ • x).1 = (τ • x).1 := congrArg Subtype.val (Subtype.ext_iff.mp h)
      rw [smul_def, smul_def] at h1
      apply Equiv.ext
      intro a
      obtain ⟨c, hc⟩ := x.2 a
      have h2 := congrFun h1 c
      rw [hc] at h2
      exact h2
    · rintro ⟨y, σ, hσ⟩
      exact ⟨σ, by simp [hσ]⟩
  rw [← Nat.card_eq_of_bijective _ hbij, card_G4]

lemma card_quot_Rel10 : Nat.card (Quot Rel10) = 34105 := by
  classical
  have hequiv : Nat.card (Quot Rel10)
      = Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) Surj10) :=
    Nat.card_congr (Quot.congr (Equiv.refl _) (fun a b => rel10_iff_orbitRel a b))
  rw [hequiv]
  have _inst : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) Surj10) := Fintype.ofFinite _
  have key : Nat.card Surj10 =
      ∑ _ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) Surj10, 24 := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits (Equiv.Perm (Fin 4)) Surj10),
      Nat.card_sigma]
    exact Finset.sum_congr rfl (fun ω _ => card_orbit _)
  rw [card_Surj10] at key
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at key
  rw [Nat.card_eq_fintype_card]
  omega

/-- A retraction of the 12 children onto 10 "units" (each sibling pair becoming one unit). -/
lemma exists_section (s₁ s₂ t₁ t₂ : Fin 12)
    (h_dist : s₁ ≠ s₂ ∧ t₁ ≠ t₂ ∧ s₁ ≠ t₁ ∧ s₁ ≠ t₂ ∧ s₂ ≠ t₁ ∧ s₂ ≠ t₂) :
    ∃ (emb : Fin 12 → Fin 10) (sec : Fin 10 → Fin 12),
      (∀ j, emb (sec j) = j) ∧ emb s₁ = emb s₂ ∧ emb t₁ = emb t₂ ∧
      (∀ f : Fin 12 → Fin 4, f s₁ = f s₂ → f t₁ = f t₂ → ∀ x, f (sec (emb x)) = f x) := by
  obtain ⟨h12, h34, h13, h14, h23, h24⟩ := h_dist
  classical
  set S : Finset (Fin 12) := ({s₂, t₂} : Finset (Fin 12))ᶜ with hS
  have hmem : ∀ x : Fin 12, x ∈ S ↔ (x ≠ s₂ ∧ x ≠ t₂) := by
    intro x; simp [hS]
  have hcard : Fintype.card {x : Fin 12 // x ∈ S} = 10 := by
    rw [Fintype.card_coe, hS, Finset.card_compl,
      Finset.card_insert_of_notMem (by simp [h24]), Finset.card_singleton]
    simp
  set rho : Fin 12 → Fin 12 := fun x => if x = s₂ then s₁ else if x = t₂ then t₁ else x with hrho
  have hrhomem : ∀ x, rho x ∈ S := by
    intro x
    by_cases hx : x = s₂
    · simp [hrho, hx, hmem, h12, h14]
    · by_cases hy : x = t₂
      · simp [hrho, hy, hmem, Ne.symm h23, h34, Ne.symm h24]
      · simp [hrho, hx, hy, hmem]
  obtain ⟨e⟩ : Nonempty ({x : Fin 12 // x ∈ S} ≃ Fin 10) := ⟨Fintype.equivFinOfCardEq hcard⟩
  refine ⟨fun x => e ⟨rho x, hrhomem x⟩,
    fun j => ((e.symm j : {x : Fin 12 // x ∈ S}) : Fin 12), ?_, ?_, ?_, ?_⟩
  · intro j
    have hne := (hmem _).mp (e.symm j).2
    have h1 : (⟨rho ((e.symm j : {x : Fin 12 // x ∈ S}) : Fin 12), hrhomem _⟩ :
        {x : Fin 12 // x ∈ S}) = e.symm j :=
      Subtype.ext (by simp [hrho, hne.1, hne.2])
    simp only []
    rw [h1, Equiv.apply_symm_apply]
  · have h1 : (⟨rho s₁, hrhomem s₁⟩ : {x : Fin 12 // x ∈ S}) = ⟨rho s₂, hrhomem s₂⟩ :=
      Subtype.ext (by simp [hrho, h12, h14])
    simp only []
    rw [h1]
  · have h1 : (⟨rho t₁, hrhomem t₁⟩ : {x : Fin 12 // x ∈ S}) = ⟨rho t₂, hrhomem t₂⟩ :=
      Subtype.ext (by simp [hrho, Ne.symm h23, h34, Ne.symm h24])
    simp only []
    rw [h1]
  · intro f hf1 hf2 x
    show f ((e.symm (e ⟨rho x, hrhomem x⟩) : {x : Fin 12 // x ∈ S}) : Fin 12) = f x
    rw [Equiv.symm_apply_apply]
    by_cases hx : x = s₂
    · simp [hrho, hx, hf1]
    · by_cases hy : x = t₂
      · simp [hrho, hy, Ne.symm h24, hf2]
      · simp [hrho, hx, hy]

lemma card_eq (s₁ s₂ t₁ t₂ : Fin 12)
    (h_dist : s₁ ≠ s₂ ∧ t₁ ≠ t₂ ∧ s₁ ≠ t₁ ∧ s₁ ≠ t₂ ∧ s₂ ≠ t₁ ∧ s₂ ≠ t₂) :
    Nat.card (Quot (RelLabeled s₁ s₂ t₁ t₂)) = Nat.card (Quot Rel10) := by
  obtain ⟨emb, sec, hsec, hs, ht, hfix⟩ := exists_section s₁ s₂ t₁ t₂ h_dist
  -- the equivalence between valid labelled assignments and surjections from the 10 units
  have hto : ∀ f : ValidLabeled s₁ s₂ t₁ t₂, Function.Surjective (fun j => f.1 (sec j)) := by
    intro f a
    obtain ⟨x, hx⟩ := f.2.1 a
    refine ⟨emb x, ?_⟩
    show f.1 (sec (emb x)) = a
    rw [hfix f.1 f.2.2.1 f.2.2.2 x]
    exact hx
  have hfrom : ∀ g : Surj10,
      AllGroupsUsed (fun x => g.1 (emb x)) ∧
        SiblingsTogether s₁ s₂ t₁ t₂ (fun x => g.1 (emb x)) := by
    intro g
    refine ⟨fun a => ?_, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := g.2 a
      exact ⟨sec j, by simpa [hsec j] using hj⟩
    · simp only [hs]
    · simp only [ht]
  set E : ValidLabeled s₁ s₂ t₁ t₂ ≃ Surj10 :=
    { toFun := fun f => ⟨fun j => f.1 (sec j), hto f⟩
      invFun := fun g => ⟨fun x => g.1 (emb x), hfrom g⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        exact hfix f.1 f.2.2.1 f.2.2.2 x
      right_inv := by
        intro g
        apply Subtype.ext
        funext j
        simp only [hsec j] } with hE
  refine Nat.card_congr (Quot.congr E ?_)
  intro f₁ f₂
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, funext fun j => congrFun hσ (sec j)⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, funext fun x => ?_⟩
    have h1 : σ (f₁.1 (sec (emb x))) = f₂.1 (sec (emb x)) := congrFun hσ (emb x)
    rw [hfix f₁.1 f₁.2.2.1 f₁.2.2.2 x] at h1
    rw [h1, hfix f₂.1 f₂.2.2.1 f₂.2.2.2 x]

end Bona49

/-- **Main result.** There are `34105` ways of dividing `12` children into four nonempty
playgroups without separating either of the two pairs of siblings. -/
theorem bona_4
    (s₁ s₂ t₁ t₂ : Fin 12)
    (h_dist :
      s₁ ≠ s₂ ∧ t₁ ≠ t₂ ∧
      s₁ ≠ t₁ ∧ s₁ ≠ t₂ ∧ s₂ ≠ t₁ ∧ s₂ ≠ t₂) :
    Nat.card (ValidUnlabeledReps s₁ s₂ t₁ t₂) = 34105 := by
  show Nat.card (Quot (Bona49.RelLabeled s₁ s₂ t₁ t₂)) = 34105
  rw [Bona49.card_eq s₁ s₂ t₁ t₂ h_dist, Bona49.card_quot_Rel10]

#print axioms bona_4
