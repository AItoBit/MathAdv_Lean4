import Mathlib

open MeasureTheory Filter

theorem real_analysis_15
    (μ : MeasureTheory.Measure ℝ) :
    ∃ T : ℕ →
        (MeasureTheory.Lp ℝ (2 : ENNReal) μ →L[ℝ]
          MeasureTheory.Lp ℝ (2 : ENNReal) μ),
      (∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ, ∀ᵐ x ∂μ,
         (T n f) x =
           (1 + Real.sin ((n : ℝ) * x) / (n : ℝ)) * f x) ∧
      (∃ M : ℝ, ∀ n : ℕ, ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
         ‖T n f‖ ≤ M * ‖f‖) := by

  let m : ℕ → ℝ → ℝ :=
    fun n x =>
      1 + Real.sin ((n : ℝ) * x) / (n : ℝ)

  have hm_cont : ∀ n : ℕ, Continuous (m n) := by
    intro n
    dsimp [m]
    fun_prop

  have hm_bound : ∀ n : ℕ, ∀ x : ℝ, |m n x| ≤ 2 := by
    intro n x
    by_cases hn : n = 0

    · subst n
      simp [m]

    · have hn_nat : 1 ≤ n :=
        Nat.one_le_iff_ne_zero.mpr hn

      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn_nat

      have hn_pos : (0 : ℝ) < (n : ℝ) := by
        linarith

      have hsin :
          |Real.sin ((n : ℝ) * x)| ≤ 1 := by
        rw [abs_le]
        constructor
        · exact Real.neg_one_le_sin _
        · exact Real.sin_le_one _

      have hs :
          |Real.sin ((n : ℝ) * x) / (n : ℝ)| ≤ 1 := by
        rw [abs_div, abs_of_pos hn_pos]
        apply (div_le_one hn_pos).2
        exact le_trans hsin hn_real

      dsimp [m]

      calc
        |1 + Real.sin ((n : ℝ) * x) / (n : ℝ)|
            ≤ |(1 : ℝ)| +
                |Real.sin ((n : ℝ) * x) / (n : ℝ)| := by
              exact abs_add_le _ _
        _ ≤ 1 + 1 := by
              have h1 : |(1 : ℝ)| ≤ 1 := by
                norm_num
              exact add_le_add h1 hs
        _ = 2 := by
              norm_num

  have hm_meas :
      ∀ n : ℕ, AEStronglyMeasurable (m n) μ := by
    intro n
    exact (hm_cont n).aestronglyMeasurable

  have hmul_mem :
      ∀ n : ℕ,
        ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
          MemLp
            (fun x => m n x * f x)
            (2 : ENNReal) μ := by
    intro n f

    have hmeas :
        AEStronglyMeasurable
          (fun x => m n x * f x) μ := by
      exact
        (hm_meas n).fun_mul
          (MeasureTheory.Lp.memLp f).aestronglyMeasurable

    have htwo :
        MemLp
          (fun x => (2 : ℝ) * f x)
          (2 : ENNReal) μ := by
      exact (MeasureTheory.Lp.memLp f).const_mul 2

    apply htwo.of_le hmeas

    filter_upwards

    intro x

    have hb := hm_bound n x
    have hf0 : 0 ≤ |f x| :=
      abs_nonneg _

    simpa [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right hb hf0

  let S :
      ℕ →
        MeasureTheory.Lp ℝ (2 : ENNReal) μ →
          MeasureTheory.Lp ℝ (2 : ENNReal) μ :=
    fun n f =>
      (hmul_mem n f).toLp
        (fun x => m n x * f x)

  have hS_ae :
      ∀ n : ℕ,
        ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
          ∀ᵐ x ∂μ,
            S n f x = m n x * f x := by
    intro n f
    dsimp [S]
    exact (hmul_mem n f).coeFn_toLp

  have hS_add :
      ∀ n : ℕ,
        ∀ f g : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
          S n (f + g) = S n f + S n g := by
    intro n f g
    apply MeasureTheory.Lp.ext

    filter_upwards
      [hS_ae n (f + g),
       hS_ae n f,
       hS_ae n g,
       MeasureTheory.Lp.coeFn_add f g,
       MeasureTheory.Lp.coeFn_add (S n f) (S n g)]
      with x hfg hf hg hfg' hsum

    rw [hfg, hsum, hfg']

    change
      m n x * (f x + g x) =
        S n f x + S n g x

    rw [hf, hg]
    ring

  have hS_smul :
      ∀ n : ℕ,
        ∀ c : ℝ,
          ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
            S n (c • f) = c • S n f := by
    intro n c f
    apply MeasureTheory.Lp.ext

    filter_upwards
      [hS_ae n (c • f),
       hS_ae n f,
       MeasureTheory.Lp.coeFn_smul c f,
       MeasureTheory.Lp.coeFn_smul c (S n f)]
      with x hcf hf hcf' hout

    rw [hcf, hout, hcf']

    change
      m n x * (c * f x) =
        c * S n f x

    rw [hf]
    ring

  let L :
      ℕ →
        (MeasureTheory.Lp ℝ (2 : ENNReal) μ →ₗ[ℝ]
          MeasureTheory.Lp ℝ (2 : ENNReal) μ) :=
    fun n =>
      {
        toFun := S n
        map_add' := hS_add n
        map_smul' := hS_smul n
      }

  have hL_bound :
      ∀ n : ℕ,
        ∀ f : MeasureTheory.Lp ℝ (2 : ENNReal) μ,
          ‖L n f‖ ≤ 2 * ‖f‖ := by
    intro n f

    apply le_trans
      (MeasureTheory.Lp.norm_le_norm_of_ae_le
        (f := L n f)
        (g := (2 : ℝ) • f) ?_)

    · simpa using norm_smul_le (2 : ℝ) f

    · filter_upwards
        [hS_ae n f,
         MeasureTheory.Lp.coeFn_smul (2 : ℝ) f]
        with x hTx h2f

      change ‖L n f x‖ ≤ ‖((2 : ℝ) • f) x‖

      change ‖S n f x‖ ≤ ‖((2 : ℝ) • f) x‖

      rw [hTx, h2f]

      have hb := hm_bound n x
      have hf0 : 0 ≤ |f x| :=
        abs_nonneg _

      simpa [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right hb hf0

  let T :
      ℕ →
        (MeasureTheory.Lp ℝ (2 : ENNReal) μ →L[ℝ]
          MeasureTheory.Lp ℝ (2 : ENNReal) μ) :=
    fun n =>
      (L n).mkContinuous 2 (hL_bound n)

  refine ⟨T, ?_, ⟨2, ?_⟩⟩

  · intro n f

    have h := hS_ae n f

    filter_upwards [h] with x hx

    simpa [T, L, S, m] using hx

  · intro n f
    change ‖(L n).mkContinuous 2 (hL_bound n) f‖ ≤
      2 * ‖f‖
    simpa using hL_bound n f
