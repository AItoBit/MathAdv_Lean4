import Mathlib

noncomputable def f (x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + 1)

theorem problem_statement :
    (∀ x y : ℝ, ‖f x - f y‖ ≤ ‖x - y‖) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      ∃ x₀ y₀ : ℝ,
        ‖f x₀ - f y₀‖ >
          α * ‖x₀ - y₀‖) := by
  constructor

  · intro x y

    rw [Real.norm_eq_abs, Real.norm_eq_abs]

    let sx : ℝ := Real.sqrt (x ^ 2 + 1)
    let sy : ℝ := Real.sqrt (y ^ 2 + 1)

    change |sx - sy| ≤ |x - y|

    have hx_nonneg :
        0 ≤ x ^ 2 + 1 := by
      nlinarith [sq_nonneg x]

    have hy_nonneg :
        0 ≤ y ^ 2 + 1 := by
      nlinarith [sq_nonneg y]

    have hsx_nonneg :
        0 ≤ sx := by
      dsimp [sx]
      exact Real.sqrt_nonneg _

    have hsy_nonneg :
        0 ≤ sy := by
      dsimp [sy]
      exact Real.sqrt_nonneg _

    have hsx_sq :
        sx ^ 2 = x ^ 2 + 1 := by
      dsimp [sx]
      exact Real.sq_sqrt hx_nonneg

    have hsy_sq :
        sy ^ 2 = y ^ 2 + 1 := by
      dsimp [sy]
      exact Real.sq_sqrt hy_nonneg

    have hsx_ge :
        |x| ≤ sx := by
      calc
        |x| = Real.sqrt (x ^ 2) := by
          symm
          exact Real.sqrt_sq_eq_abs x
        _ ≤ Real.sqrt (x ^ 2 + 1) := by
          exact Real.sqrt_le_sqrt (by linarith)
        _ = sx := by
          rfl

    have hsy_ge :
        |y| ≤ sy := by
      calc
        |y| = Real.sqrt (y ^ 2) := by
          symm
          exact Real.sqrt_sq_eq_abs y
        _ ≤ Real.sqrt (y ^ 2 + 1) := by
          exact Real.sqrt_le_sqrt (by linarith)
        _ = sy := by
          rfl

    have hxy_abs :
        x * y ≤ |x| * |y| := by
      calc
        x * y ≤ |x * y| :=
          le_abs_self (x * y)
        _ = |x| * |y| := by
          exact abs_mul x y

    have habs_prod :
        |x| * |y| ≤ sx * sy := by
      exact
        mul_le_mul
          hsx_ge
          hsy_ge
          (abs_nonneg y)
          hsx_nonneg

    have hxy :
        x * y ≤ sx * sy :=
      le_trans hxy_abs habs_prod

    have hsq :
        (sx - sy) ^ 2 ≤
          (x - y) ^ 2 := by
      nlinarith [hsx_sq, hsy_sq, hxy]

    have hsq_abs :
        |sx - sy| ^ 2 ≤
          |x - y| ^ 2 := by
      simpa [sq_abs] using hsq

    exact
      (sq_le_sq₀
        (abs_nonneg (sx - sy))
        (abs_nonneg (x - y))).mp hsq_abs

  · intro α hα hα1

    have hden :
        0 < 1 - α := by
      linarith

    let x₀ : ℝ :=
      2 / (1 - α)

    let y₀ : ℝ :=
      0

    have hx₀_pos :
        0 < x₀ := by
      dsimp [x₀]
      exact div_pos (by norm_num) hden

    have hden_ne :
        1 - α ≠ 0 :=
      ne_of_gt hden

    have hx₀_rel :
        x₀ * (1 - α) = 2 := by
      dsimp [x₀]
      field_simp [hden_ne]

    have hx₀_gt_one :
        1 < x₀ := by
      nlinarith [hx₀_rel]

    have hx₀_sq_nonneg :
        0 ≤ x₀ ^ 2 :=
      sq_nonneg x₀

    have hsqrt_gt :
        x₀ <
          Real.sqrt (x₀ ^ 2 + 1) := by
      calc
        x₀ = Real.sqrt (x₀ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
          exact (abs_of_pos hx₀_pos).symm
        _ < Real.sqrt (x₀ ^ 2 + 1) := by
          exact
            Real.sqrt_lt_sqrt
              hx₀_sq_nonneg
              (by linarith)

    have hdiff_pos :
        0 <
          Real.sqrt (x₀ ^ 2 + 1) - 1 := by
      linarith

    have hsharp :
        α * x₀ <
          Real.sqrt (x₀ ^ 2 + 1) - 1 := by
      have haux :
          α * x₀ < x₀ - 1 := by
        nlinarith [hx₀_rel]
      linarith

    refine ⟨x₀, y₀, ?_⟩

    simp only [f, y₀]
    norm_num

    rw [
      abs_of_pos hx₀_pos,
      abs_of_pos hdiff_pos
    ]

    exact hsharp
