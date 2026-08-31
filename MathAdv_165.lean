import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# A Riemannian immersion of an `n`-manifold (`n ≥ 3`) into `ℝ^{n+1}` cannot have
all sectional curvatures negative

The mathematical content of this statement is entirely pointwise and linear-algebraic.
For an isometric immersion of an `n`-manifold into `ℝ^{n+1}`, the Gauss equation says that
for a tangent plane spanned by orthonormal vectors `u`, `v` the sectional curvature equals
`⟪A u, u⟫ * ⟪A v, v⟫ - ⟪A u, v⟫ ^ 2`, where `A` is the (self-adjoint) shape operator of the
hypersurface at the point, i.e. the second fundamental form with respect to a unit normal.
This is `gaussSectionalCurvature` below.

Diagonalising `A` in an orthonormal eigenbasis with principal curvatures `κ 1, …, κ n`, the
sectional curvature of the coordinate plane spanned by the `i`-th and `j`-th eigenvector is
`κ i * κ j`.  If all sectional curvatures were negative we would need `κ i * κ j < 0` for all
`i ≠ j`, which is impossible as soon as there are three indices: among three reals, two must
have the same sign (`no_three_reals_pairwise_negative_products`).

Hence the correct reasoning for the original problem is (c): the Gauss equation for a
hypersurface in `ℝ^{n+1}` together with a sign argument on products of principal curvatures.
-/

namespace Hypersurface

/-- The sectional curvature, as given by the Gauss equation, of the plane spanned by two
orthonormal tangent vectors `u`, `v` of a hypersurface of Euclidean space whose shape
operator (second fundamental form with respect to a unit normal) is `A`. -/
noncomputable def gaussSectionalCurvature {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ[ℝ] E) (u v : E) : ℝ :=
  ⟪A u, u⟫_ℝ * ⟪A v, v⟫_ℝ - ⟪A u, v⟫_ℝ ^ 2

/-- Among any three real numbers, two of them have a product which is `≥ 0`:
one cannot have all three pairwise products negative. -/
theorem no_three_reals_pairwise_negative_products (a b c : ℝ)
    (hab : a * b < 0) (hac : a * c < 0) (hbc : b * c < 0) : False := by
  nlinarith [sq_nonneg (a * b * c), mul_pos (mul_pos_of_neg_of_neg hab hac) (neg_pos.2 hbc)]

/-- The Gauss equation evaluated on a plane spanned by two distinct principal directions:
the sectional curvature is the product of the two corresponding principal curvatures. -/
theorem gaussSectionalCurvature_eigenvectorBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) {i j : Fin n} (hij : i ≠ j) :
    gaussSectionalCurvature A (hA.eigenvectorBasis hn i) (hA.eigenvectorBasis hn j)
      = hA.eigenvalues hn i * hA.eigenvalues hn j := by
  have horth := (hA.eigenvectorBasis hn).orthonormal
  have hij' : ⟪hA.eigenvectorBasis hn i, hA.eigenvectorBasis hn j⟫_ℝ = 0 :=
    horth.2 hij
  have hii : ⟪hA.eigenvectorBasis hn i, hA.eigenvectorBasis hn i⟫_ℝ = 1 := by simp
  have hjj : ⟪hA.eigenvectorBasis hn j, hA.eigenvectorBasis hn j⟫_ℝ = 1 := by simp
  simp only [gaussSectionalCurvature, hA.apply_eigenvectorBasis hn, real_inner_smul_left,
    hij', hii, hjj]
  norm_num

/-- **Main theorem (pointwise form).**  Let `E` be the tangent space at a point of a
hypersurface of Euclidean space, of dimension at least `3`, and let `A` be the shape operator
there (a self-adjoint endomorphism).  Then not all sectional curvatures, computed by the Gauss
equation, can be negative. -/
theorem not_all_sectional_curvatures_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    ¬ (∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → gaussSectionalCurvature A u v < 0) := by
  intro hneg
  set n := Module.finrank ℝ E with hn'
  have hn : Module.finrank ℝ E = n := rfl
  set b := hA.eigenvectorBasis hn with hb
  have hkey : ∀ i j : Fin n, i ≠ j →
      hA.eigenvalues hn i * hA.eigenvalues hn j < 0 := by
    intro i j hij
    have := hneg (b i) (b j) (b.orthonormal.1 i) (b.orthonormal.1 j) (b.orthonormal.2 hij)
    rwa [gaussSectionalCurvature_eigenvectorBasis hA hn hij] at this
  -- three distinct indices exist since `n ≥ 3`
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have h2 : (2 : ℕ) < n := by omega
  refine no_three_reals_pairwise_negative_products
    (hA.eigenvalues hn ⟨0, h0⟩) (hA.eigenvalues hn ⟨1, h1⟩) (hA.eigenvalues hn ⟨2, h2⟩)
    (hkey _ _ ?_) (hkey _ _ ?_) (hkey _ _ ?_) <;>
  · simp [Fin.ext_iff]

/-- **Answer to the computational question.**  There is no Riemannian immersion of a
`4`-manifold into `ℝ^5` with all sectional curvatures negative: already at a single point,
no self-adjoint shape operator on a `4`-dimensional tangent space produces only negative
sectional curvatures via the Gauss equation. -/
theorem no_neg_curved_hypersurface_dim_four
    (A : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4)) (hA : A.IsSymmetric) :
    ¬ (∀ u v : EuclideanSpace ℝ (Fin 4), ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 →
        gaussSectionalCurvature A u v < 0) := by
  refine not_all_sectional_curvatures_neg ?_ A hA
  simp

end Hypersurface

/-
The statement as originally proposed used opaque predicates:

  opaque IsRiemannianImmersion ... : Prop
  opaque HasAllSectionalCurvaturesNegative ... : Prop

  theorem geometry_20 (n : ℕ) (M : Type*) ... (hn : n ≥ 3)
      (f : M → EuclideanSpace ℝ (Fin (n + 1))) (h_imm : IsRiemannianImmersion f) :
      ¬ HasAllSectionalCurvaturesNegative f

Since `opaque` constants carry no mathematical content, that statement is not provable (nor
refutable): it asserts nothing about immersions or curvature.  The faithful formalization of
the mathematics is given above, where the Gauss equation for a hypersurface of `ℝ^{n+1}` is
taken as the definition of the sectional curvature in terms of the shape operator.
-/
