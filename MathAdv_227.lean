import Mathlib

/-- Teorema (number_theory_4_9, Q227 / question_10):
    No existen soluciones enteras a la ecuación diofántica x² - 15y² = 3. -/
theorem question_10 :
    ¬ ∃ x y : ℤ, x^2 - 15 * y^2 = 3 := by
  rintro ⟨x, y, h⟩
  -- 1) De x² - 15y² = 3 deducimos que 3 ∣ x²
  have h3_dvd_xsq : 3 ∣ x^2 := by
    use 5 * y^2 + 1
    linear_combination h

  -- 2) Como 3 es primo, 3 ∣ x² implica 3 ∣ x
  have h3_prime : Prime (3 : ℤ) := by norm_num
  have h3_dvd_x : 3 ∣ x := Prime.dvd_of_dvd_pow h3_prime h3_dvd_xsq

  -- 3) Escribimos x = 3 * k y sustituimos en la ecuación original
  rcases h3_dvd_x with ⟨k, rfl⟩
  have h_div3 : 3 * (3 * k^2 - 5 * y^2) = 3 * 1 := by
    calc
      3 * (3 * k^2 - 5 * y^2) = (3 * k)^2 - 15 * y^2 := by ring
      _ = 3 := h
      _ = 3 * 1 := by ring

  have h_eq : 3 * k^2 - 5 * y^2 = 1 :=
    mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) h_div3

  -- 4) Estudiamos la ecuación 3k² - 5y² = 1 módulo 5.
  -- Usamos los posibles restos de k dividido entre 5.
  have hk_cases : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
    have h1 : 0 ≤ k % 5 := Int.emod_nonneg k (by decide)
    have h2 : k % 5 < 5 := Int.emod_lt_of_pos k (by decide)
    omega

  rcases hk_cases with hk0 | hk1 | hk2 | hk3 | hk4
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m := ⟨k / 5, by omega⟩
    subst hm
    have : 3 * (5 * m)^2 - 5 * y^2 = 5 * (15 * m^2 - y^2) := by ring
    rw [this] at h_eq
    omega
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m + 1 := ⟨k / 5, by omega⟩
    subst hm
    have : 3 * (5 * m + 1)^2 - 5 * y^2 = 5 * (15 * m^2 + 6 * m - y^2) + 3 := by ring
    rw [this] at h_eq
    omega
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m + 2 := ⟨k / 5, by omega⟩
    subst hm
    have : 3 * (5 * m + 2)^2 - 5 * y^2 = 5 * (15 * m^2 + 12 * m - y^2 + 2) + 2 := by ring
    rw [this] at h_eq
    omega
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m + 3 := ⟨k / 5, by omega⟩
    subst hm
    have : 3 * (5 * m + 3)^2 - 5 * y^2 = 5 * (15 * m^2 + 18 * m - y^2 + 5) + 2 := by ring
    rw [this] at h_eq
    omega
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m + 4 := ⟨k / 5, by omega⟩
    subst hm
    have : 3 * (5 * m + 4)^2 - 5 * y^2 = 5 * (15 * m^2 + 24 * m - y^2 + 9) + 3 := by ring
    rw [this] at h_eq
    omega
