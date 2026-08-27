import Mathlib

theorem Gallian_7_alt
    (G : Type _) [Group G]
    (h_nonab : ¬ ∀ a b : G, a * b = b * a) :
    ¬ IsCyclic (MulAut G) := by
  intro h_cyc
  have := h_cyc
  apply h_nonab
  set f : G →* MulAut G := MulAut.conj with hf
  
  -- 1. Elements in the kernel of conjugation commute with all elements
  have hcen : ∀ u : G, f u = 1 → ∀ w : G, u * w = w * u := by
    intro u hu w
    have h : (f u) w = w := by rw [hu]; rfl
    rw [hf, MulAut.conj_apply] at h
    calc u * w = (u * w * u⁻¹) * u := by group
      _ = w * u := by rw [h]
      
  -- 2. Inn(G) is cyclic, so it has a generator γ = f a
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := f.range)
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp γ.2
  
  -- 3. Every x is a power of a times a central element
  have key : ∀ x : G, ∃ (m : ℤ) (z : G), (∀ w : G, z * w = w * z) ∧ x = a ^ m * z := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (hγ (⟨f x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : f.range))
    have hm' : ((γ : MulAut G)) ^ m = f x := by
      have := congrArg Subtype.val hm; simpa using this
    have hfa : f (a ^ m) = f x := by rw [map_zpow, ha, hm']
    refine ⟨m, (a ^ m)⁻¹ * x, ?_, by group⟩
    refine hcen _ ?_
    rw [map_mul, map_inv, hfa, inv_mul_cancel]
    
  -- 4. Using the decomposition, show that any two elements commute
  intro x y
  obtain ⟨m, z, hz, hx⟩ := key x
  obtain ⟨n, v, hv, hy⟩ := key y
  subst hx; subst hy
  have e1 : a ^ m * z * (a ^ n * v) = a ^ m * a ^ n * (z * v) := by
    simp only [mul_assoc]; congr 1
    rw [← mul_assoc, hz (a ^ n), mul_assoc]
  have e2 : a ^ n * v * (a ^ m * z) = a ^ n * a ^ m * (v * z) := by
    simp only [mul_assoc]; congr 1
    rw [← mul_assoc, hv (a ^ m), mul_assoc]
  rw [e1, e2, ← zpow_add, ← zpow_add, add_comm m n, hz v]
