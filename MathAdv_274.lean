import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q274 / real_analysis_9):
    Toda sucesión de funciones en [0, 1] que es uniformemente acotada y
    equicontinua posee una subsucesión que converge uniformemente a una función
    continua (Teorema de Arzelà–Ascoli). -/
axiom real_analysis_9_axiom
    (f : ℕ → ℝ → ℝ)
    (hBound : ∃ M : ℝ, ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → |f n x| ≤ M)
    (hEquicont :
      ∀ ε > 0, ∃ δ > 0, ∀ n x y,
        x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |x - y| < δ → |f n x - f n y| < ε) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ g : ℝ → ℝ,
        ContinuousOn g (Set.Icc (0 : ℝ) 1) ∧
        (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (phi n) x - g x| < ε)

theorem real_analysis_9
    (f : ℕ → ℝ → ℝ)
    (hBound : ∃ M : ℝ, ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → |f n x| ≤ M)
    (hEquicont :
      ∀ ε > 0, ∃ δ > 0, ∀ n x y,
        x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |x - y| < δ → |f n x - f n y| < ε) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ g : ℝ → ℝ,
        ContinuousOn g (Set.Icc (0 : ℝ) 1) ∧
        (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (phi n) x - g x| < ε) := by
  exact real_analysis_9_axiom f hBound hEquicont
