import Mathlib

namespace RetosMatematicos

theorem Gallian_9
    (R : Type*) [NonUnitalCommSemiring R] [Nontrivial R]
    (h : ∀ {a : R}, a ≠ 0 → ∀ r : R, ∃ s : R, a * s = r) :
    ∃ e : R,
      (∀ x : R, e * x = x ∧ x * e = x) ∧
      (∀ {a : R}, a ≠ 0 → ∃ b : R, a * b = e ∧ b * a = e) := by
  -- Pick any nonzero `a`; since `aR = R`, there is `e` with `a * e = a`.
  obtain ⟨a, ha⟩ := exists_ne (0 : R)
  obtain ⟨e, he⟩ := h ha a
  -- `e` is a left identity: every `x` is of the form `a * s`.
  have key : ∀ x : R, e * x = x := by
    intro x
    obtain ⟨s, hs⟩ := h ha x
    calc e * x = e * (a * s) := by rw [hs]
      _ = (e * a) * s := (mul_assoc _ _ _).symm
      _ = (a * e) * s := by rw [mul_comm e a]
      _ = a * s := by rw [he]
      _ = x := hs
  refine ⟨e, fun x => ⟨key x, by rw [mul_comm]; exact key x⟩, ?_⟩
  -- Inverses: apply the hypothesis to the target `e`.
  intro b hb
  obtain ⟨c, hc⟩ := h hb e
  exact ⟨c, hc, by rw [mul_comm]; exact hc⟩

end RetosMatematicos
