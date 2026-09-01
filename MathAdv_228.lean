import Mathlib

open MeasureTheory Set

/-- Teorema (probabilities_4_9, Q228 / problem_1a):
    Dos eventos sobre las componentes independientes x e y en el espacio producto
    de probabilidad son independientes: μ(A ∩ B) = μ(A) * μ(B). -/
theorem problem_1a
    (μx μy : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μx]
    [MeasureTheory.IsProbabilityMeasure μy] :
    let μ : MeasureTheory.Measure (ℝ × ℝ) := MeasureTheory.Measure.prod μx μy
    μ ({ω : ℝ × ℝ | ω.1 > (1 : ℝ) / 3} ∩ {ω : ℝ × ℝ | ω.2 > (2 : ℝ) / 3})
      = μ {ω : ℝ × ℝ | ω.1 > (1 : ℝ) / 3}
        * μ {ω : ℝ × ℝ | ω.2 > (2 : ℝ) / 3} := by
  intro μ
  -- Definimos los conjuntos unidimensionales
  let S : Set ℝ := {x : ℝ | x > (1 : ℝ) / 3}
  let T : Set ℝ := {y : ℝ | y > (2 : ℝ) / 3}

  -- 1) Igualdades de conjuntos como productos cartesianos
  have h_inter : {ω : ℝ × ℝ | ω.1 > (1 : ℝ) / 3} ∩ {ω : ℝ × ℝ | ω.2 > (2 : ℝ) / 3} = S ×ˢ T := by
    ext ⟨a, b⟩
    simp [S, T]

  have h_left : {ω : ℝ × ℝ | ω.1 > (1 : ℝ) / 3} = S ×ˢ Set.univ := by
    ext ⟨a, b⟩
    simp [S]

  have h_right : {ω : ℝ × ℝ | ω.2 > (2 : ℝ) / 3} = Set.univ ×ˢ T := by
    ext ⟨a, b⟩
    simp [T]

  -- 2) Sustituimos las formas de producto cartesiano y evaluamos la medida producto
  rw [h_inter, h_left, h_right]
  change (μx.prod μy) (S ×ˢ T) = (μx.prod μy) (S ×ˢ Set.univ) * (μx.prod μy) (Set.univ ×ˢ T)
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [measure_univ, measure_univ]
  rw [mul_one, one_mul]
