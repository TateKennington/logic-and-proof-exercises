section
  variables A B : Prop
  variable h : A ∧ B

  example: B ∧ A :=
    and.intro (and.right h) (and.left h)
end

section
  variables Q R : Prop
  variable h: Q

  example: (Q → R) → R :=
    assume h1, h1 h
end

section
  variables A B: Prop

  example: ¬(A ∧ B) → (A → ¬B):=
    assume h,
    assume h1,
    assume h2,
      show false, from h (and.intro h1 h2)
end

section
  variables P Q R S T: Prop
  variable h1: (P ∧ Q) ∧ R
  variable h2: S ∧ T

  example: Q ∧ S:=
    and.intro
      (and.right (and.left h1))
      (and.left h2)
end

section
  variables A B C: Prop

  example: (A → C) ∧ (B → ¬C) → ¬(A ∧ B) :=
    assume h,
    assume h1,
     show false, from
      (and.right h) (and.right h1) ((and.left h) (and.left h1))
end

section
  variables A B C: Prop

  example: (A ∧ B) → ((A → C) → ¬(B → ¬C)) := 
    assume h1,
    assume h2,
    assume h3,
     show false, from
      h3 (and.right h1) (h2 (and.left h1))
end

section
  variables A B: Prop

  example: A ∨ B → B ∨ A :=
    assume h,
      show B ∨ A, from or.elim h
        (assume h1: A, show B ∨ A, from or.inr h1)
        (assume h1: B, show B ∨ A, from or.inl h1)
end

section
  variables A B: Prop

  example: ¬A ∧ ¬B → ¬(A ∨ B) := 
    assume h1,
    assume h2,
      show false, from or.elim h2
        (assume h3: A, (and.left h1) h3)
        (assume h3: B, (and.right h1) h3)
end

section
  variables A B: Prop
  variable h: ¬A ∨ ¬B

  example: ¬(A ∧ B) :=
    assume h1,
      show false, from or.elim h
        (assume h2: ¬A, h2 (and.left h1))
        (assume h2: ¬B, h2 (and.right h1))
end

section
  variable A: Prop

  example: ¬(A ↔ ¬A) :=
    assume h: A ↔ ¬A,
    show false, from
      have hₐ: ¬A, from
        assume h₁: A,
        have h₂: A → ¬A, from iff.elim_left h, 
        show false, from h₂ h₁ h₁,
      have h₁: ¬A → A, from iff.elim_right h,
      hₐ (h₁ hₐ)
end

section
  variables A B: Prop
  variable h: A ↔ B

  example: ¬A ↔ ¬B :=
    have h₁: ¬A → ¬B, from
      assume hₐ,
      show ¬B, from
        assume hₐb,
        show false, from
          have h₂: B → A, from iff.elim_right h,
          hₐ (h₂ hₐb),
    have h₃: ¬B → ¬A, from
      assume hₐb,
      show ¬A, from
        assume hₐ,
        show false, from
          have h₂: A → B, from iff.elim_left h,
          hₐb (h₂ hₐ),
    iff.intro h₁ h₃
end

section
  variables P Q R: Prop
  variable h: (P ∨ Q) → R

  example: P → R :=
    assume hₚ,
    show R, from
      have h₁: (P ∨ Q), from or.intro_left Q hₚ,
      h h₁
end

section
  variables P Q R: Prop

  example: ((P ∨ Q) → R) → (P → R) :=
    assume h,
    assume hₚ,
    show R, from
      have h₁: (P ∨ Q), from or.intro_left Q hₚ,
      h h₁
end

section
  variables A B C: Prop
  variable h: A ∨ B

  example: C → (A ∨ B) ∧ C :=
    assume hₐc,
    and.intro h hₐc 
end

section
  variables W X Y Z: Prop
  variable h₁: W → X
  variable h₂: Y → Z

  example: W ∨ Y → X ∨ Z :=
    assume h,
    have h₃: W → X ∨ Z, from
      assume w,
      show X ∨ Z, from or.intro_left Z (h₁ w),
    have h₄: Y → X ∨ Z, from
      assume y,
      show X ∨ Z, from or.intro_right X (h₂ y),
    or.elim h h₃ h₄
end

section
  variables A B: Prop
  
  example: (A ∨ (B ∧ A)) → A :=
   assume h,
   show A, from
    have h₁: A → A, from assume hₐ, hₐ,
    have h₂: (B ∧ A) → A, from assume hₐ, and.right hₐ,
    or.elim h h₁ h₂
end