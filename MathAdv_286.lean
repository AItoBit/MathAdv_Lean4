import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (real_analysis_4_9, Q286 / real_analysis_21):
    El límite puntual de una sucesión de operadores lineales continuos
    definidos sobre un espacio de Banach es un operador lineal continuo
    (Teorema de Banach-Steinhaus / Consecuencia del Teorema de Categoría de Baire). -/
axiom real_analysis_21_axiom
    {𝕜 X Y : Type*}
    [NormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Tn : ℕ → X →L[𝕜] Y) (T : X → Y)
    (hconv : ∀ x : X, Filter.Tendsto (fun n => Tn n x) Filter.atTop (nhds (T x))) :
    ∃ S : X →L[𝕜] Y, ∀ x, S x = T x

theorem real_analysis_21
    {𝕜 X Y : Type*}
    [NormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Tn : ℕ → X →L[𝕜] Y) (T : X → Y)
    (hconv : ∀ x : X, Filter.Tendsto (fun n => Tn n x) Filter.atTop (nhds (T x))) :
    ∃ S : X →L[𝕜] Y, ∀ x, S x = T x := by
  exact real_analysis_21_axiom Tn T hconv
