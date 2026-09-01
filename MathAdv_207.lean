import Mathlib

/-- Marco abstracto para teorías aritméticas que admiten numeración de Gödel
y el Lema de Autorreferencia / Diagonalización de Gödel. -/
structure ArithmeticTheory (Sentence Formula1 : Type) where
  code : Sentence → ℕ
  subst : Formula1 → ℕ → Sentence
  not : Sentence → Sentence
  iff : Sentence → Sentence → Sentence
  and : Sentence → Sentence → Sentence
  -- Demostrabilidad en la teoría base N y en la extensión A
  provableN : Sentence → Prop
  provableA : Sentence → Prop
  -- N es una subteoría de A (A extiende a N)
  subtheory : ∀ {s : Sentence}, provableN s → provableA s
  -- Consistencia de A: A no puede demostrar simultáneamente p y ¬p
  consistentA : ∀ {s : Sentence}, ¬ (provableA s ∧ provableA (not s))
  -- Reglas proposicionales básicas
  iff_elim_l : ∀ {p q : Sentence}, provableN (iff p q) → provableN p → provableN q
  iff_elim_r : ∀ {p q : Sentence}, provableN (iff p q) → provableN q → provableN p
  iff_elim_l_A : ∀ {p q : Sentence}, provableA (iff p q) → provableA p → provableA q
  iff_elim_r_A : ∀ {p q : Sentence}, provableA (iff p q) → provableA q → provableA p
  -- Lema de Autorreferencia / Diagonal de Gödel en N:
  -- Para toda fórmula con una variable libre ψ, existe una sentencia δ tal que
  -- N ⊢ δ ↔ ψ(⌜δ⌝).
  diagonal_lemma : ∀ (ψ : Formula1), ∃ (δ : Sentence),
    provableN (iff δ (subst ψ (code δ)))

/-- Teorema de no-representabilidad de Thm_A en N (Gödel / Tarski):
Si A es una extensión consistente de N y N satisface el Lema Diagonal,
entonces Thm_A no es fuertemente representable por ninguna fórmula γ en N. -/
theorem godel_thmA_not_representable
    {Sentence Formula1 : Type}
    (T : ArithmeticTheory Sentence Formula1)
    (notF1 : Formula1 → Formula1)
    (h_subst_not : ∀ (γ : Formula1) (n : ℕ),
      T.subst (notF1 γ) n = T.not (T.subst γ n)) :
    ¬ ∃ (γ : Formula1),
        (∀ (f : Sentence), T.provableA f → T.provableN (T.subst γ (T.code f))) ∧
        (∀ (f : Sentence), ¬ T.provableA f → T.provableN (T.not (T.subst γ (T.code f)))) := by
  rintro ⟨γ, h_repr_pos, h_repr_neg⟩

  -- 1. Aplicamos el Lema Diagonal a la fórmula negada ¬γ:
  -- Existe una sentencia G tal que N ⊢ G ↔ ¬γ(⌜G⌝).
  obtain ⟨G, hG_diag⟩ := T.diagonal_lemma (notF1 γ)
  rw [h_subst_not γ (T.code G)] at hG_diag

  -- Puesto que A extiende a N, A también demuestra la equivalencia de punto fijo
  have hG_diag_A : T.provableA (T.iff G (T.not (T.subst γ (T.code G)))) :=
    T.subtheory hG_diag

  -- 2. Evaluamos si A ⊢ G:
  by_cases hA_G : T.provableA G
  · -- Caso 1: A ⊢ G
    -- Por representabilidad positiva, N ⊢ γ(⌜G⌝) y por tanto A ⊢ γ(⌜G⌝)
    have hN_gamma : T.provableN (T.subst γ (T.code G)) := h_repr_pos G hA_G
    have hA_gamma : T.provableA (T.subst γ (T.code G)) := T.subtheory hN_gamma
    -- A partir de A ⊢ G y el punto fijo, obtenemos A ⊢ ¬γ(⌜G⌝)
    have hA_not_gamma : T.provableA (T.not (T.subst γ (T.code G))) :=
      T.iff_elim_l_A hG_diag_A hA_G
    -- Contradicción directa con la consistencia de A
    exact T.consistentA ⟨hA_gamma, hA_not_gamma⟩

  · -- Caso 2: A ⊬ G
    -- Por representabilidad negativa, N ⊢ ¬γ(⌜G⌝)
    have hN_not_gamma : T.provableN (T.not (T.subst γ (T.code G))) := h_repr_neg G hA_G
    -- Por la equivalencia del punto fijo en N, N ⊢ G
    have hN_G : T.provableN G := T.iff_elim_r hG_diag hN_not_gamma
    -- Dado que A extiende a N, tenemos A ⊢ G, contradiciendo A ⊬ G
    have hA_G_contra : T.provableA G := T.subtheory hN_G
    exact hA_G hA_G_contra
