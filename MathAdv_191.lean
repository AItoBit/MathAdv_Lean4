import Mathlib

/-! ## Syntax -/

inductive NiceTerm where
  | a : NiceTerm
  | b : NiceTerm
  | c : NiceTerm
  | d : NiceTerm
  | comp : NiceTerm → NiceTerm → NiceTerm
  deriving Repr

/-- Concrete syntax of a nice term, as a list of characters. -/
def render : NiceTerm → List Char
  | .a => ['a']
  | .b => ['b']
  | .c => ['c']
  | .d => ['d']
  | .comp s₁ s₂ => '[' :: (render s₁ ++ '∘' :: (render s₂ ++ [']']))

/-- Number of occurrences of `c` in a string. -/
def countChar (c : Char) : List Char → Nat
  | [] => 0
  | e :: l => (if e = c then 1 else 0) + countChar c l

/-- `s` is a proper initial segment of `t`. -/
def IsProperInitialSegment (s t : List Char) : Prop :=
  s ≠ [] ∧ s.length < t.length ∧ s <+: t

/-! ## Arithmetic of `countChar` -/

@[simp] theorem countChar_nil (c : Char) : countChar c [] = 0 := rfl

theorem countChar_cons_self (c : Char) (l : List Char) :
    countChar c (c :: l) = 1 + countChar c l := by
  simp [countChar]

theorem countChar_cons_ne {c e : Char} (h : e ≠ c) (l : List Char) :
    countChar c (e :: l) = countChar c l := by
  simp [countChar, h]

theorem countChar_append (c : Char) (l₁ l₂ : List Char) :
    countChar c (l₁ ++ l₂) = countChar c l₁ + countChar c l₂ := by
  induction l₁ with
  | nil => simp
  | cons e l ih => simp only [List.cons_append, countChar, ih, Nat.add_assoc]

/-! ## Prefix combinatorics -/

theorem prefix_singleton_eq {x : Char} {s : List Char} (h : s <+: [x]) (hne : s ≠ []) :
    s = [x] := by
  obtain ⟨v, hv⟩ := h
  cases s with
  | nil => exact absurd rfl hne
  | cons f s' =>
    simp only [List.cons_append, List.cons.injEq] at hv
    obtain ⟨rfl, hv2⟩ := hv
    cases s' with
    | nil => rfl
    | cons g s'' => simp at hv2

/-- A prefix of `l₁ ++ l₂` either sits inside `l₁`, or covers `l₁` entirely. -/
theorem prefix_append_cases (l₂ : List Char) :
    ∀ (l₁ s : List Char), s <+: l₁ ++ l₂ →
      s <+: l₁ ∨ ∃ u, s = l₁ ++ u ∧ u <+: l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro s h
    exact Or.inr ⟨s, by simp, by simpa using h⟩
  | cons e l ih =>
    intro s h
    cases s with
    | nil => exact Or.inl ⟨e :: l, by simp⟩
    | cons f s' =>
      obtain ⟨v, hv⟩ := h
      simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, hv2⟩ := hv
      rcases ih s' ⟨v, hv2⟩ with h1 | ⟨u, hu1, hu2⟩
      · obtain ⟨w, hw⟩ := h1
        exact Or.inl ⟨w, by simp [hw]⟩
      · exact Or.inr ⟨u, by simp [hu1], hu2⟩

/-! ## A full term is balanced -/

theorem countChar_open_comp (t₁ t₂ : NiceTerm) :
    countChar '[' (render (NiceTerm.comp t₁ t₂))
      = 1 + countChar '[' (render t₁) + countChar '[' (render t₂) := by
  simp only [render]
  rw [countChar_cons_self, countChar_append,
    countChar_cons_ne (show ('∘' : Char) ≠ '[' by decide),
    countChar_append, countChar_cons_ne (show (']' : Char) ≠ '[' by decide),
    countChar_nil]
  omega

theorem countChar_close_comp (t₁ t₂ : NiceTerm) :
    countChar ']' (render (NiceTerm.comp t₁ t₂))
      = countChar ']' (render t₁) + countChar ']' (render t₂) + 1 := by
  simp only [render]
  rw [countChar_cons_ne (show ('[' : Char) ≠ ']' by decide), countChar_append,
    countChar_cons_ne (show ('∘' : Char) ≠ ']' by decide),
    countChar_append, countChar_cons_self, countChar_nil]
  omega

theorem render_balanced (t : NiceTerm) :
    countChar '[' (render t) = countChar ']' (render t) := by
  induction t with
  | a => decide
  | b => decide
  | c => decide
  | d => decide
  | comp t₁ t₂ ih₁ ih₂ =>
    rw [countChar_open_comp, countChar_close_comp, ih₁, ih₂]
    omega

/-! ## Main result, by structural induction -/

theorem countChar_lt_of_prefix (t : NiceTerm) :
    ∀ s : List Char, s <+: render t → s ≠ [] → s ≠ render t →
      countChar ']' s < countChar '[' s := by
  induction t with
  | a =>
    intro s hp hne hne2
    simp only [render] at hp hne2
    exact absurd (prefix_singleton_eq hp hne) hne2
  | b =>
    intro s hp hne hne2
    simp only [render] at hp hne2
    exact absurd (prefix_singleton_eq hp hne) hne2
  | c =>
    intro s hp hne hne2
    simp only [render] at hp hne2
    exact absurd (prefix_singleton_eq hp hne) hne2
  | d =>
    intro s hp hne hne2
    simp only [render] at hp hne2
    exact absurd (prefix_singleton_eq hp hne) hne2
  | comp t₁ t₂ ih₁ ih₂ =>
    -- every prefix of a full term has at least as many `[` as `]`
    have ge₁ : ∀ u : List Char, u <+: render t₁ → countChar ']' u ≤ countChar '[' u := by
      intro u hu
      by_cases h1 : u = []
      · subst h1; simp
      · by_cases h2 : u = render t₁
        · subst h2; exact Nat.le_of_eq (render_balanced t₁).symm
        · exact Nat.le_of_lt (ih₁ u hu h1 h2)
    have ge₂ : ∀ u : List Char, u <+: render t₂ → countChar ']' u ≤ countChar '[' u := by
      intro u hu
      by_cases h1 : u = []
      · subst h1; simp
      · by_cases h2 : u = render t₂
        · subst h2; exact Nat.le_of_eq (render_balanced t₂).symm
        · exact Nat.le_of_lt (ih₂ u hu h1 h2)
    intro s hp hne hne2
    simp only [render] at hp hne2
    obtain ⟨v, hv⟩ := hp
    cases s with
    | nil => exact absurd rfl hne
    | cons f s' =>
      simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, hv2⟩ := hv
      have hs' : s' <+: render t₁ ++ '∘' :: (render t₂ ++ [']']) := ⟨v, hv2⟩
      have hne3 : s' ≠ render t₁ ++ '∘' :: (render t₂ ++ [']']) := by
        intro hcon
        exact hne2 (by rw [hcon])
      have key : countChar ']' s' ≤ countChar '[' s' := by
        rcases prefix_append_cases _ _ _ hs' with h1 | ⟨u, hu1, hu2⟩
        · exact ge₁ s' h1
        · subst hu1
          have hu : countChar ']' u ≤ countChar '[' u := by
            cases u with
            | nil => simp
            | cons g u' =>
              obtain ⟨w, hw⟩ := hu2
              simp only [List.cons_append, List.cons.injEq] at hw
              obtain ⟨rfl, hw2⟩ := hw
              rw [countChar_cons_ne (show ('∘' : Char) ≠ ']' by decide),
                countChar_cons_ne (show ('∘' : Char) ≠ '[' by decide)]
              have hu' : u' <+: render t₂ ++ [']'] := ⟨w, hw2⟩
              rcases prefix_append_cases _ _ _ hu' with h2 | ⟨w', hw'1, hw'2⟩
              · exact ge₂ u' h2
              · have hw'nil : w' = [] := by
                  by_contra hcon
                  exact hne3 (by rw [hw'1, prefix_singleton_eq hw'2 hcon])
                rw [hw'1, hw'nil, List.append_nil]
                exact Nat.le_of_eq (render_balanced t₂).symm
          rw [countChar_append, countChar_append, render_balanced t₁]
          omega
      rw [countChar_cons_self, countChar_cons_ne (show ('[' : Char) ≠ ']' by decide)]
      omega

/-- Any proper initial segment of a nice term has more `[` than `]`. -/
theorem nice_term_initial_segment (t : NiceTerm) {s : List Char}
    (h : IsProperInitialSegment s (render t)) :
    countChar ']' s < countChar '[' s := by
  obtain ⟨hne, hlen, hpre⟩ := h
  have hne2 : s ≠ render t := by
    intro hcon
    rw [hcon] at hlen
    exact Nat.lt_irrefl _ hlen
  exact countChar_lt_of_prefix t s hpre hne hne2
