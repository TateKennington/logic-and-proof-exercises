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

section
  open classical
  variables P Q R: Prop
  variable h: ¬P → (Q ∨ R)
  variable nQ: ¬Q
  variables nR: ¬R

  example: P :=
    have nnP: ¬P → false, from
      assume : ¬P,
      have Q ∨ R, from h this,
      have h₁: Q → false, from
        assume :Q, nQ this,
      have h₂: R → false, from
        assume :R, nR this,
      show false, from or.elim ‹Q ∨ R› h₁ h₂,
    show P, from by_contradiction nnP
end

section
  open classical
  variables A B: Prop
  variable h: A → B

  example: ¬A ∨ B :=
    have h₁: A ∨ ¬A, from em A,
    have h₂: ¬A → ¬A ∨ B, from 
      assume :¬A, or.intro_left B this,
    have h₃: A → ¬A ∨ B, from
      assume :A, or.intro_right (¬A) (h this),
    or.elim h₁ h₃ h₂
end

section
  open classical
  variables A B: Prop

  example: A → ((A ∧ B) ∨ (A ∧ ¬B)):=
    assume :A,
    have emB: B ∨ ¬B, from em B,
    have h₁: B → ((A ∧ B) ∨ (A ∧ ¬B)), from
      assume :B,
      have h_and: A ∧ B, from and.intro ‹A› ‹B›,
      or.intro_left (A ∧ ¬B) h_and,
    have h₂: ¬B → ((A ∧ B) ∨ (A ∧ ¬B)), from
      assume :¬B,
      have h_and: A ∧ ¬B, from and.intro ‹A› ‹¬B›,
      or.intro_right (A ∧ B) h_and,
    or.elim emB h₁ h₂
end

section
  open classical
  variables {A B C : Prop}

  lemma step1 (h₁ : ¬ (A ∧ B)) (h₂ : A) : ¬ A ∨ ¬ B :=
  have ¬ B, from
    assume :B,
    have A ∧ B, from and.intro h₂ ‹B›,
    h₁ this,
  show ¬ A ∨ ¬ B, from or.inr this

  lemma step2 (h₁ : ¬ (A ∧ B)) (h₂ : ¬ (¬ A ∨ ¬ B)) : false :=
  have ¬ A, from
    assume : A,
    have ¬ A ∨ ¬ B, from step1 h₁ ‹A›,
    show false, from h₂ this,
  show false, from
    have ¬ A ∨ ¬ B, from or.inl ‹¬A›,
    h₂ this

  theorem step3 (h : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
  by_contradiction
    (assume h' : ¬ (¬ A ∨ ¬ B),
      show false, from step2 h h')
end

section
  open classical
  variables {A B C : Prop}

  example (h : ¬ B → ¬ A) : A → B :=
    assume :A,
    show B, from
      have h₁: ¬B → false, from
        assume :¬B,
        have ¬A, from h this,
        this ‹A›,
      by_contradiction h₁

  example (h : A → B) : ¬ A ∨ B :=
    have h₁: ¬(¬ A ∨ B) → false, from
      assume h₂:¬(¬ A ∨ B),
      have ¬A, from
        assume :A,
        have B, from h this,
        have ¬A ∨ B, from or.inr ‹B›,
        h₂ this,
      have ¬A ∨ B, from or.inl ‹¬A›,
      h₂ this,
    by_contradiction h₁
end