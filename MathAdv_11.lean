import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- The additive group `ℚ` has no proper subgroup of finite index.

Proof (via Lagrange's theorem): if `H ≤ ℚ` has finite index `n`, then the quotient
group `ℚ ⧸ H` has order `n`, so `n • q ∈ H` for every rational `q`.  Applying this
to `q / n` gives `q ∈ H`, hence `H = ⊤`. -/
theorem Gallian_12 :
  ¬ ∃ H : AddSubgroup ℚ, H.FiniteIndex ∧ H ≠ ⊤ := by
  rintro ⟨H, hfin, hne⟩
  apply hne
  rw [AddSubgroup.eq_top_iff']
  intro q
  have hn : H.index ≠ 0 := hfin.index_ne_zero
  have h := H.nsmul_index_mem (q / (H.index : ℚ))
  have hq : H.index • (q / (H.index : ℚ)) = q := by
    rw [nsmul_eq_mul]
    field_simp
  rwa [hq] at h
