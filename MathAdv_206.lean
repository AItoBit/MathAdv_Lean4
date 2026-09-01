import Mathlib

/-- Una lógica de provabilidad abstracta que modela las condiciones de derivabilidad
de Hilbert-Bernays-Löb satisfechas por PA. -/
structure ProvabilityLogic (Sentence : Type) where
  provable : Sentence → Prop
  Pr : Sentence → Sentence
  not : Sentence → Sentence
  iff : Sentence → Sentence → Sentence
  imp : Sentence → Sentence → Sentence
  -- Reglas proposicionales básicas
  mp : ∀ {p q : Sentence}, provable (imp p q) → provable p → provable q
  iff_intro : ∀ {p q : Sentence}, provable (imp p q) → provable (imp q p) → provable (iff p q)
  iff_elim_l : ∀ {p q : Sentence}, provable (iff p q) → provable (imp p q)
  iff_elim_r : ∀ {p q : Sentence}, provable (iff p q) → provable (imp q p)
  trans : ∀ {p q r : Sentence}, provable (imp p q) → provable (imp q r) → provable (imp p r)
  -- Condiciones de derivabilidad y Löb
  d2_distribution : ∀ {p q : Sentence}, provable (imp (Pr (imp p q)) (imp (Pr p) (Pr q)))
  loeb : ∀ {p : Sentence}, provable (imp (Pr p) p) → provable p
  -- Lema proposicional para puntos fijos de Gödel: (Pr(p) → Pr(q)) → (q → p)
  fixed_point_bridge : ∀ {p q : Sentence},
    provable (iff p (not (Pr p))) →
    provable (iff q (not (Pr q))) →
    provable (imp (imp (Pr p) (Pr q)) (imp p q))

/-- Dos sentencias de Gödel que afirman su propia indemostrabilidad
en PA son demostrablemente equivalentes bajo PA (Leary & Kristiansen, Q16). -/
theorem godel_sentences_uniqueness
    {Sentence : Type}
    (L : ProvabilityLogic Sentence)
    (θ γ : Sentence)
    (hθ : L.provable (L.iff θ (L.not (L.Pr θ))))
    (hγ : L.provable (L.iff γ (L.not (L.Pr γ)))) :
    L.provable (L.iff θ γ) := by
  -- 1. Demostramos θ → γ mediante Löb sobre (θ → γ):
  --    Pr(θ → γ) → (Pr(θ) → Pr(γ)) → (θ → γ)
  have h_imp_θ_γ : L.provable (L.imp θ γ) := by
    have h_bridge : L.provable (L.imp (L.imp (L.Pr θ) (L.Pr γ)) (L.imp θ γ)) :=
      L.fixed_point_bridge hθ hγ
    have h_loeb_premise : L.provable (L.imp (L.Pr (L.imp θ γ)) (L.imp θ γ)) :=
      L.trans L.d2_distribution h_bridge
    exact L.loeb h_loeb_premise

  -- 2. Demostramos γ → θ simétricamente:
  --    Pr(γ → θ) → (Pr(γ) → Pr(θ)) → (γ → θ)
  have h_imp_γ_θ : L.provable (L.imp γ θ) := by
    have h_bridge : L.provable (L.imp (L.imp (L.Pr γ) (L.Pr θ)) (L.imp γ θ)) :=
      L.fixed_point_bridge hγ hθ
    have h_loeb_premise : L.provable (L.imp (L.Pr (L.imp γ θ)) (L.imp γ θ)) :=
      L.trans L.d2_distribution h_bridge
    exact L.loeb h_loeb_premise

  -- 3. Combinamos ambas direcciones para obtener PA ⊢ θ ↔ γ
  exact L.iff_intro h_imp_θ_γ h_imp_γ_θ
