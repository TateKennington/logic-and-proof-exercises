open classical

variables A B P Q: Prop

example: ¬(¬A ∨ B) → A :=
  assume h,
  have ¬A → false, from
    assume nA,
    have ¬A ∨ B, from or.inl nA,
    h this,
  by_contradiction this

example: (¬P ∧ ¬Q) → ¬(P ∨ Q) :=
  assume h,
  assume h_or,
  show false, from
    have nP: ¬P, from and.left h,
    have nQ: ¬Q, from and.right h,
    have h₁: P → false, from assume :P, nP this,
    have h₂: Q → false, from assume :Q, nQ this,
    or.elim h_or h₁ h₂
