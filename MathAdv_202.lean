import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.ElementarySubstructure
import Mathlib.SetTheory.Cardinal.Basic

open FirstOrder
open FirstOrder.Language

/-- Ningún conjunto de sentencias de primer orden `Sigma` en un lenguaje `L`
puede caracterizar una estructura infinita `A` módulo isomorfismo,
ya que por el teorema de Löwenheim-Skolem hacia arriba existen modelos de
cardinalidad estrictamente mayor que satisfacen exactamente las mismas sentencias. -/
theorem Leary_Kristiansen_12
    (L : FirstOrder.Language)
    (A : Type) [IA : L.Structure A]
    (hAinf : Infinite A) :
    ¬ ∃ (Sigma : L.Theory),
        ∀ (B : Type) [IB : L.Structure B],
          (Nonempty (L.Equiv B A)) ↔
          (∀ (sent : L.Sentence), Sigma sent →
             @Sentence.Realize L B IB sent) := by
  rintro ⟨Sigma, hSigma⟩

  -- Tomamos un cardinal κ estrictamente mayor que el cardinal de A
  -- y mayor o igual al cardinal del lenguaje L.
  let κ := Cardinal.succ (Cardinal.max (#A) (#L.Functions + #L.Relations + ℵ₀))
  have hlt : #A < κ := by
    apply lt_of_le_of_lt (Cardinal.le_max_left (#A) _)
    exact Cardinal.lt_succ _

  -- 1. A satisface su propia caracterización Sigma
  have hA_models : ∀ sent, Sigma sent → @Sentence.Realize L A IA sent := by
    intro sent hsent
    exact ((hSigma A).1 ⟨L.Equiv.refl L A⟩) sent hsent

  -- 2. Por Löwenheim-Skolem hacia arriba / extensión elemental,
  -- existe un modelo B de Sigma (elementalmente equivalente a A) con cardinal κ.
  have h_ex : ∃ (B : Type) (IB : L.Structure B),
      (#B = κ) ∧ (∀ sent, Sigma sent → @Sentence.Realize L B IB sent) := by
    -- Mathlib proporciona la existencia de modelos elementales de cardinal κ arbitrario
    -- sobre la teoría completa de A.
    obtain ⟨B, IB, hB_card, hB_models⟩ :=
      Theory.exists_model_card_eq (L.completeTheory A) κ
        (by
          -- κ es mayor o igual a max(#L, ℵ₀)
          dsimp [κ]
          exact le_trans (Cardinal.le_max_right _ _) (Cardinal.le_succ _))
        ⟨A, inferInstance, Theory.completeTheory.models A⟩
    refine ⟨B, IB, hB_card, ?_⟩
    intro sent hsent
    have h_in_complete : sent ∈ L.completeTheory A := by
      rw [L.mem_completeTheory]
      exact hA_models sent hsent
    exact hB_models sent h_in_complete

  obtain ⟨B, IB, hB_card, hB_models⟩ := h_ex

  -- 3. Por la hipótesis de caracterización, B debe ser isomorfo a A
  have h_iso : Nonempty (L.Equiv B A) := (hSigma B).2 hB_models
  rcases h_iso with ⟨e⟩

  -- 4. Un isomorfismo de estructuras implica una biyección entre sus tipos portadores
  have h_card_eq : #B = #A := Cardinal.mk_congr e.toEquiv

  -- 5. Contradicción: #B = κ > #A = #B
  rw [hB_card] at h_card_eq
  exact (ne_of_gt hlt) h_card_eq.symm
