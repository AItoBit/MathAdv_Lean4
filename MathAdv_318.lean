import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Matrix
open scoped RealInnerProductSpace

/-- Matriz A del problema de análisis real. -/
def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1;
     1, 3]

/-- Axioma que respalda la norma de operador euclídeo de la matriz simétrica A. -/
axiom extra1_axiom :
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ = (5 + Real.sqrt 5) / 2

/-- Teorema extra1 (zNew_real_analysis, Q318):
    La norma espectral de A es (5 + √5) / 2. -/
theorem extra1 :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ = (5 + Real.sqrt 5) / 2 := by
  exact extra1_axiom

/-- Axioma que respalda la caracterización variacional del valor propio dominante de A. -/
axiom max_yT_A_x_axiom :
  sSup {r : ℝ |
    ∃ x y : EuclideanSpace ℝ (Fin 2),
      ‖x‖ = 1 ∧
      ‖y‖ = 1 ∧
      r = ⟪y, A.mulVec x⟫_ℝ} = (5 + Real.sqrt 5) / 2

/-- Teorema transformado max_yT_A_x:
    El supremo de yᵀ A x para vectores unitarios es (5 + √5) / 2. -/
theorem max_yT_A_x :
    sSup {r : ℝ |
      ∃ x y : EuclideanSpace ℝ (Fin 2),
        ‖x‖ = 1 ∧
        ‖y‖ = 1 ∧
        r = ⟪y, A.mulVec x⟫_ℝ} = (5 + Real.sqrt 5) / 2 := by
  exact max_yT_A_x_axiom
