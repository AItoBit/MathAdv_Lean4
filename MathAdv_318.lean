import Mathlib

open scoped Matrix

noncomputable section

theorem extra1 :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 3]
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ =
      (5 + Real.sqrt 5) / 2 := by

  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![2, 1;
       1, 3]

  let T :
      EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2) :=
    (Matrix.toEuclideanCLM :
      Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ]
          EuclideanSpace ℝ (Fin 2))) A

  have hT :
      LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin A) = T := by
    apply ContinuousLinearMap.ext
    intro x
    change (Matrix.toEuclideanLin A) x = T x
    have hx :=
      congrArg
        (fun f => f x)
        (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A)
    simpa [T] using hx.symm

  change
    ‖LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin A)‖ =
      (5 + Real.sqrt 5) / 2

  rw [hT]
