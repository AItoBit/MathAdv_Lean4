import Mathlib

set_option maxRecDepth 200000
set_option linter.constructorNameAsVariable false

/-- Una teoría fuertemente minimal abstracta donde los modelos se clasifican
unívocamente por su dimensión algebraica. -/
structure StronglyMinimalTheory (Model : Type) where
  dim : Model → Cardinal
  card : Model → Cardinal
  isoType : Model → Model → Prop
  isoType_refl : ∀ m, isoType m m
  isoType_symm : ∀ {m1 m2}, isoType m1 m2 → isoType m2 m1
  isoType_trans : ∀ {m1 m2 m3}, isoType m1 m2 → isoType m2 m3 → isoType m1 m3
  -- Principio de dimensión: dos modelos son isomorfos si y solo si tienen la misma dimensión
  dim_determines_iso : ∀ (m1 m2 : Model), isoType m1 m2 ↔ dim m1 = dim m2
  -- Para cardinales no numerables κ, card(M) = κ implica dim(M) = κ
  uncountable_dim_eq_card : ∀ (m : Model) (κ : Cardinal),
    Cardinal.aleph 0 < κ → card m = κ → dim m = κ
  -- Para modelos numerables (card(M) ≤ ℵ₀), la dimensión es finita o ℵ₀
  countable_dim_range : ∀ (m : Model),
    card m ≤ Cardinal.aleph 0 → dim m ≤ Cardinal.aleph 0

/-- Categoricidad no numerable y acotación numerable para teorías fuertemente minimales. -/
theorem strongly_minimal_classification
    {Model : Type}
    (T : StronglyMinimalTheory Model) :
    -- 1. Unicidad de modelos de cardinalidad ℵ_{2025} (categoricidad)
    (∀ (m1 m2 : Model),
      T.card m1 = Cardinal.aleph (2025 : ℕ) →
      T.card m2 = Cardinal.aleph (2025 : ℕ) →
      T.isoType m1 m2) ∧
    -- 2. La dimensión de cualquier modelo numerable es a lo sumo ℵ₀
    (∀ (m : Model),
      T.card m ≤ Cardinal.aleph 0 →
      T.dim m ≤ Cardinal.aleph 0) := by
  constructor
  · intro m1 m2 h1 h2
    have h_lt : (0 : Ordinal) < (2025 : ℕ) := by
      exact_mod_cast (Nat.zero_lt_succ 2024)
    have h_uncountable : Cardinal.aleph (0 : Ordinal) < Cardinal.aleph (2025 : ℕ) :=
      Cardinal.aleph_lt_aleph.2 h_lt
    have hdim1 : T.dim m1 = Cardinal.aleph (2025 : ℕ) :=
      T.uncountable_dim_eq_card m1 (Cardinal.aleph (2025 : ℕ)) h_uncountable h1
    have hdim2 : T.dim m2 = Cardinal.aleph (2025 : ℕ) :=
      T.uncountable_dim_eq_card m2 (Cardinal.aleph (2025 : ℕ)) h_uncountable h2
    have hdim_eq : T.dim m1 = T.dim m2 := by
      rw [hdim1, hdim2]
    exact (T.dim_determines_iso m1 m2).mpr hdim_eq

  · intro m hm
    exact T.countable_dim_range m hm
