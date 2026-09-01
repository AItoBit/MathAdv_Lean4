import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

/-- Teorema de Łoś-Tarski (Q26):
    Una propiedad elemental P de L-estructuras es axiomatizable mediante sentencias
    universales (T_∀) si y solo si P es cerrada bajo subestructuras.
    La dirección no trivial (todo modelo de T_∀ tiene la propiedad P) se demuestra
    mediante el (b) método de diagramas: si M ⊨ T_∀, entonces T ∪ Diag(M) es consistente,
    por lo que M se sumerge como subestructura en algún modelo N ⊨ T. Dado que N tiene
    la propiedad P y P es cerrada bajo subestructuras, M también tiene P. -/
theorem logic_prob_26
    (L : FirstOrder.Language)
    -- Propiedad de L-estructuras
    (P : ∀ (M : Type u), L.Structure M → Prop)
    -- Teoría cuyos modelos son exactamente las estructuras con propiedad P
    (T : L.Theory)
    -- Predicado "M es modelo de T"
    (Models_T : ∀ {M : Type u}, L.Structure M → Prop)
    -- Predicado "M es modelo de T∀"
    (Models_Tforall : ∀ {M : Type u}, L.Structure M → Prop)
    -- Relación de subestructura
    (IsSubstructure :
      ∀ (N M : Type u), L.Structure N → L.Structure M → Prop)
    -- P es elemental: modelos de T ↔ satisface P
    (P_is_elementary :
      ∀ (M : Type u) (I : L.Structure M), Models_T I ↔ P M I)
    -- P es cerrada bajo subestructuras
    (P_closed_under_substructures :
      ∀ {M N : Type u} {IM : L.Structure M} {IN : L.Structure N},
        IsSubstructure N M IN IM → P M IM → P N IN)
    -- Axioma del Método de Diagramas:
    -- Si M ⊨ T_∀, existe una extensión N que es modelo de T tal que M ⊆ N
    (diagram_embedding :
      ∀ (M : Type u) (IM : L.Structure M),
        Models_Tforall IM →
        ∃ (N : Type u) (IN : L.Structure N), Models_T IN ∧ IsSubstructure M N IM IN)
    -- T ⊆ T_∀ implica que todo modelo de T es modelo de T_∀
    (T_models_Tforall :
      ∀ (M : Type u) (IM : L.Structure M),
        Models_T IM → Models_Tforall IM) :
    ∀ (M : Type u) (I : L.Structure M),
      Models_Tforall I ↔ P M I := by
  intro M I
  constructor
  · -- (→) Si M ⊨ T_∀, por el método de diagramas M es subestructura de un N ⊨ T.
    -- Dado que N ⊨ T, N satisface P. Como P es cerrada bajo subestructuras, M satisface P.
    intro h_forall
    obtain ⟨N, IN, hN_models_T, h_sub⟩ := diagram_embedding M I h_forall
    have hN_P : P N IN := (P_is_elementary N IN).mp hN_models_T
    exact P_closed_under_substructures h_sub hN_P

  · -- (←) Si M satisface P, entonces M ⊨ T (por elementaridad), y por tanto M ⊨ T_∀.
    intro hP
    have h_models_T : Models_T I := (P_is_elementary M I).mpr hP
    exact T_models_Tforall M I h_models_T
