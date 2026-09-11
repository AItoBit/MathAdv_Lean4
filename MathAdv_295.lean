import Mathlib

abbrev Circle2 :=
  {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1}

abbrev Torus2 :=
  Circle2 × Circle2

def torusAntipode (p : Torus2) : Torus2 :=
  (⟨-p.1.1, by simpa using p.1.2⟩,
   ⟨-p.2.1, by simpa using p.2.2⟩)

theorem Hatcher_1_1_8_counterexample :
    ∃ f : Torus2 → EuclideanSpace ℝ (Fin 2),
      Continuous f ∧
      ∀ p : Torus2, f (torusAntipode p) ≠ f p := by

  refine ⟨fun p => p.1.1, ?_, ?_⟩

  · exact continuous_subtype_val.comp continuous_fst

  · intro p

    change -p.1.1 ≠ p.1.1

    intro hneg

    have hsum :
        0 = p.1.1 + p.1.1 := by
      have h :=
        congrArg (fun z => z + p.1.1) hneg
      simpa using h

    have htwo :
        (2 : ℝ) • p.1.1 = 0 := by
      rw [two_smul]
      exact hsum.symm

    have hz :
        p.1.1 = 0 := by
      rcases smul_eq_zero.mp htwo with h2 | hx
      · norm_num at h2
      · exact hx

    have hnorm := p.1.2

    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
