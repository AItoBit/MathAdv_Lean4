import Mathlib

open MeasureTheory Filter Topology

/-!
# Weak convergence of mesa-truncated probability densities

Let `f` be a probability density on `ℝ` and let `M_k(x) := m_{-+}(x; -k, k, ε)` be the mesa
function with fixed `0 < ε ≤ 1`.  Then `M_1 f, M_2 f, …` converges weakly to `f`.

The only properties of the mesa function that are used are:

* `0 ≤ m_{-+}(x; a, b, ε) ≤ 1` for all `x`;
* for each fixed `x`, `m_{-+}(x; -k, k, ε) → 1` as `k → ∞`;
* measurability of `x ↦ m_{-+}(x; -k, k, ε)`.

Accordingly, the mesa function is kept abstract as a parameter `mesa` subject to these
hypotheses.  The proof is an application of the Lebesgue dominated convergence theorem, with
dominating function `C * f`, where `C` bounds the test function.
-/

/-- The `k`-th mesa multiplier `x ↦ m_{-+}(x; -k, k, ε)`. -/
def mesaFun_kammler27
    (mesa : ℝ → ℝ → ℝ → ℝ → ℝ)
    (ε : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  mesa x (-(k : ℝ)) (k : ℝ) ε

/-- The truncated density `M_k f`. -/
def Mkf_kammler27
    (mesa : ℝ → ℝ → ℝ → ℝ → ℝ)
    (ε : ℝ) (f : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  mesaFun_kammler27 mesa ε k x * f x

/-- Weak convergence of a sequence of densities `u k` to `f`: testing against every bounded
continuous function converges. -/
def weakConverges_kammler27 (u : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (phi : ℝ → ℝ),
    Continuous phi →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |phi x| ≤ C) →
    Filter.Tendsto (fun k : ℕ => ∫ x : ℝ, phi x * u k x) Filter.atTop
      (nhds (∫ x : ℝ, phi x * f x))

/-- A nonnegative function whose integral equals `1` is integrable. -/
theorem integrable_of_integral_eq_one_kammler27
    {f : ℝ → ℝ} (h_prob : ∫ x : ℝ, f x = 1) : Integrable f := by
  by_contra h
  rw [integral_undef h] at h_prob
  norm_num at h_prob

/-- **Weak convergence of the mesa truncations of a probability density.**

If `f ≥ 0` has `∫ f = 1` and `mesa` is measurable in its first argument, takes values in `[0,1]`
and satisfies `m_{-+}(x; -k, k, ε) → 1` pointwise, then `M_k f → f` weakly.  The proof is the
Lebesgue dominated convergence theorem.  (The hypothesis `0 < ε ≤ 1` is part of the statement of
the problem but is not needed for the argument.) -/
theorem kammler_27
    (f : ℝ → ℝ)
    (h_nonneg : ∀ x, 0 ≤ f x)
    (h_prob : ∫ x : ℝ, f x = 1)
    (mesa : ℝ → ℝ → ℝ → ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1)
    (h_mesa_meas :
      ∀ k : ℕ, Measurable (fun x : ℝ => mesa x (-(k : ℝ)) (k : ℝ) ε))
    (h_mesa_bounds :
      ∀ x a b ε, 0 ≤ mesa x a b ε ∧ mesa x a b ε ≤ 1)
    (h_mesa_tendsto :
      ∀ x : ℝ,
        Filter.Tendsto (fun k : ℕ => mesa x (-(k : ℝ)) (k : ℝ) ε)
          Filter.atTop (nhds 1)) :
    weakConverges_kammler27 (Mkf_kammler27 mesa ε f) f := by
  intro phi hphi ⟨C, hC0, hC⟩
  have hf : Integrable f := integrable_of_integral_eq_one_kammler27 h_prob
  refine tendsto_integral_of_dominated_convergence (fun x => C * f x) ?_ ?_ ?_ ?_
  · intro k
    exact ((hphi.measurable.aestronglyMeasurable).mul
      (((h_mesa_meas k).aestronglyMeasurable).mul hf.aestronglyMeasurable))
  · exact hf.const_mul C
  · intro k
    filter_upwards with x
    have h1 : |mesa x (-(k : ℝ)) (k : ℝ) ε * f x| ≤ f x := by
      rw [abs_of_nonneg (mul_nonneg (h_mesa_bounds _ _ _ _).1 (h_nonneg x))]
      calc mesa x (-(k : ℝ)) (k : ℝ) ε * f x ≤ 1 * f x :=
            mul_le_mul_of_nonneg_right (h_mesa_bounds _ _ _ _).2 (h_nonneg x)
        _ = f x := one_mul _
    calc ‖phi x * Mkf_kammler27 mesa ε f k x‖
        = |phi x| * |mesa x (-(k : ℝ)) (k : ℝ) ε * f x| := by
          simp [Mkf_kammler27, mesaFun_kammler27, Real.norm_eq_abs, abs_mul]
      _ ≤ C * f x := by
          exact mul_le_mul (hC x) h1 (abs_nonneg _) hC0
  · filter_upwards with x
    have : Tendsto (fun k : ℕ => phi x * (mesa x (-(k : ℝ)) (k : ℝ) ε * f x))
        atTop (nhds (phi x * (1 * f x))) :=
      ((h_mesa_tendsto x).mul_const (f x)).const_mul (phi x)
    simpa [Mkf_kammler27, mesaFun_kammler27] using this
