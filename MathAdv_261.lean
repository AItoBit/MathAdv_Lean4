import Mathlib

theorem problem_34
  (deck_size : ℕ) (h_deck : deck_size = 52)
  (ace_count : ℕ) (h_aces : ace_count = 4)
  (draw_size : ℕ) (h_draw : draw_size = 2) :
  let total_combinations : ℕ := Nat.choose deck_size draw_size
  let no_ace_combinations : ℕ := Nat.choose (deck_size - ace_count) draw_size
  let at_least_one_ace_combinations : ℕ := total_combinations - no_ace_combinations
  let two_ace_combinations : ℕ := Nat.choose ace_count draw_size
  (two_ace_combinations : ℚ) / at_least_one_ace_combinations ≠ 3 / 51 := by
  subst h_deck h_aces h_draw
  intro total_combinations no_ace_combinations at_least_one_ace_combinations
    two_ace_combinations
  -- C(4,2) = 6
  have h1 : two_ace_combinations = 6 := by decide
  -- C(52,2) - C(48,2) = 1326 - 1128 = 198
  have h2 : at_least_one_ace_combinations = 198 := by decide
  rw [h1, h2]
  -- 6/198 = 1/33 ≠ 1/17 = 3/51
  norm_num
