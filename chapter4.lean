variables A B C D: Prop

example : A ∧ (A → B) → B :=
  assume h,
  have A, from and.left h,
  have A → B, from and.right h,
  ‹A → B› ‹A›

example : A → ¬ (¬ A ∧ B) :=
  assume :A,
  show ¬ (¬ A ∧ B), from
    assume h,
    have nA: ¬A, from and.left h,
    nA ‹A›


example : ¬ (A ∧ B) → (A → ¬ B) :=
 assume h₁,
 assume h₂,
 show ¬B, from
  assume :B,
  have A ∧ B, from and.intro h₂ this,
  h₁ this

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
  have A → C ∨ D, from
    assume :A,
    have C, from h₂ ‹A›,
    or.inl this,
  have B → C ∨ D, from
    assume :B,
    have D, from h₃ ‹B›,
    or.inr this,
  or.elim h₁ ‹A → C ∨ D› ‹B → C ∨ D›

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
  assume nh,
  have nA: ¬A, from and.left h,
  have nB: ¬B, from and.right h,
  have h₁: A → false, from assume :A, nA this,
  have h₂: B → false, from assume :B, nB this,
  or.elim nh h₁ h₂

example : ¬ (A ↔ ¬ A) :=
  assume h: A ↔ ¬A,
  show false, from
    have hₐ: ¬A, from
      assume h₁: A,
      have h₂: A → ¬A, from iff.elim_left h, 
      show false, from h₂ h₁ h₁,
    have h₁: ¬A → A, from iff.elim_right h,
    hₐ (h₁ hₐ)