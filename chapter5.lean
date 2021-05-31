section
  variable A: Prop
  variable h: A ∨ ¬A

  example: (¬A → false) → A :=
    assume hna,
    have h₁: A → A, from assume :A, this,
    have h₂: ¬A → A, from assume :¬A, false.elim (hna this),
    or.elim h h₁ h₂
end

section
  variables A B: Prop
  variable h: ¬A ∨ ¬B

  example: ¬(A ∧ B) :=
    assume h₁,
    have ha : A, from and.left h₁,
    have hb : B, from and.right h₁,
    have h₂: ¬A → false, from assume :¬A, this ha,
    have h₃: ¬B → false, from assume :¬B, this hb,
    or.elim h h₂ h₃
end

section
  open classical

  variables A B: Prop
  variable h: ¬(A ∧ B)

  example: ¬A ∨ ¬B:=
    have A → ¬B, from
      assume :A,
      assume :B,
      have A ∧ B, from and.intro ‹A› ‹B›,
      h ‹A ∧ B›,
    have ¬(¬A ∨ ¬B) → ¬A, from
      assume h₁,
      assume :A,
      have ¬B, from ‹A → ¬B› ‹A›,
      have ¬A ∨ ¬B, from or.intro_right (¬A) ‹¬B›,
      h₁ ‹¬A ∨ ¬B›,
    have ¬(¬A ∨ ¬B) → false, from
      assume h₁,
      have ¬A, from ‹¬(¬A ∨ ¬B) → ¬A› h₁,
      have ¬A ∨ ¬B, from or.intro_left (¬B) ‹¬A›,
      h₁ ‹¬A ∨ ¬B›,
    by_contradiction ‹¬(¬A ∨ ¬B) → false›
end