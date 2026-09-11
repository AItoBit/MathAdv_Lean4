import Mathlib

/-!
# Union of convex sets with nonempty triple intersections

The requested statement `union_convex_simply_connected` is **false as written**:
for `n = 0` the hypotheses hold vacuously, but the union is empty, and
`SimplyConnectedSpace` requires a nonempty (path-connected) space.
This is proved below (`original_statement_false`).

Proved here without `sorry`:
* `original_statement_false` — the counterexample `n = 0`.
* `union_simply_connected_of_common_point` — if all sets share a point, the union is
  star-convex, hence contractible, hence simply connected.
* `union_convex_simply_connected_of_le_two` — the corrected statement (`0 < n`) in dimension
  `m ≤ 2`, via Helly's theorem (triple intersections ⇒ a common point).

The general case `m ≥ 3` needs a Seifert–van Kampen / nerve-theorem argument,
which is not available in Mathlib.
-/

namespace UnionConvex

/-- The statement as given fails for `n = 0`. -/
theorem original_statement_false :
    ¬ ∀ (m n : ℕ) (S : Fin n → Set (Fin m → ℝ)),
      (∀ i, Convex ℝ (S i)) → (∀ i j k, (S i ∩ S j ∩ S k).Nonempty) →
      SimplyConnectedSpace (⋃ i, S i) := by
  intro H
  have h := H 0 0 (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  have hpc := (simply_connected_iff_paths_homotopic.mp h).1
  obtain ⟨⟨x, hx⟩⟩ := @PathConnectedSpace.nonempty _ _ hpc
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact i.elim0

/-- If all the convex sets share a point, the union is simply connected. -/
theorem union_simply_connected_of_common_point
    (m n : ℕ) (hn : 0 < n)
    (S : Fin n → Set (Fin m → ℝ))
    (h_convex : ∀ i, Convex ℝ (S i))
    {c : Fin m → ℝ} (hc : ∀ i, c ∈ S i) :
    SimplyConnectedSpace (⋃ i, S i) := by
  have hstar : StarConvex ℝ c (⋃ i, S i) :=
    starConvex_iUnion fun i => (h_convex i).starConvex (hc i)
  have hne : (⋃ i, S i).Nonempty := ⟨c, Set.mem_iUnion.mpr ⟨⟨0, hn⟩, hc _⟩⟩
  haveI := hstar.contractibleSpace hne
  infer_instance

/-- Corrected statement (`0 < n`) in dimension `m ≤ 2`, via Helly's theorem. -/
theorem union_convex_simply_connected_of_le_two
    (m n : ℕ) (hm : m ≤ 2) (hn : 0 < n)
    (S : Fin n → Set (Fin m → ℝ))
    (h_convex : ∀ i, Convex ℝ (S i))
    (h_inter : ∀ i j k, (S i ∩ S j ∩ S k).Nonempty) :
    SimplyConnectedSpace (⋃ i, S i) := by
  classical
  have hcommon : (⋂ i ∈ (Finset.univ : Finset (Fin n)), S i).Nonempty := by
    refine Convex.helly_theorem' (𝕜 := ℝ) (fun i _ => h_convex i) ?_
    intro I _ hI
    rw [Module.finrank_fin_fun] at hI
    -- every `I` with at most three elements is covered by some `{i, j, k}`
    obtain ⟨i, j, k, hsub⟩ : ∃ i j k : Fin n, I ⊆ {i, j, k} := by
      have h3 : I.card ≤ 3 := by omega
      interval_cases h : I.card
      · refine ⟨⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩, ?_⟩
        intro x hx
        simp [Finset.card_eq_zero.mp h] at hx
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
        refine ⟨a, a, a, ?_⟩
        intro x hx
        rw [ha] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp h
        refine ⟨a, a, b, ?_⟩
        intro x hx
        rw [hab] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      · obtain ⟨a, b, d, _, _, _, habd⟩ := Finset.card_eq_three.mp h
        refine ⟨a, b, d, ?_⟩
        intro x hx
        rw [habd] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
    obtain ⟨c, hc⟩ := h_inter i j k
    refine ⟨c, Set.mem_iInter₂.mpr fun x hx => ?_⟩
    have hx' := hsub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact hc.1.1
    · exact hc.1.2
    · exact hc.2
  obtain ⟨c, hc⟩ := hcommon
  have hc' : ∀ i, c ∈ S i := fun i => Set.mem_iInter₂.mp hc i (Finset.mem_univ i)
  exact union_simply_connected_of_common_point m n hn S h_convex hc'

end UnionConvex
