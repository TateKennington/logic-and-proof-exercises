variable U: Type
variables A B C: U → Prop

section
  example: (∀x, A x → B x) → ((∀x, A x) → (∀x, B x)) :=
    assume h,
    assume all_Ax,
    assume x, 
    have Ax: A x, from all_Ax x,
    have Ax_imp_Bx: A x → B x , from h x,
    show B x, from Ax_imp_Bx Ax
end

section
  example (all_Ax_or_Bx: ∀x, A x ∨ B x) (all_nAy: ∀y, ¬A y):
  ∀x, B x :=
    assume x,
    have Ax_or_Bx: A x ∨ B x, from all_Ax_or_Bx x,
    have nAx: ¬A x, from all_nAy x,
    have h₁: A x → B x, from assume Ax: A x, false.elim (nAx Ax),
    have h₂: B x → B x, from assume Bx: B x, Bx,
    or.elim Ax_or_Bx h₁ h₂
end

section
  example: (∃x, A x) ∨ (∃x, B x) → ∃x, A x ∨ B x :=
    assume h,
    have h₁: (∃x, A x) → ∃x, A x ∨ B x, from
      assume h_ex,
      exists.elim h_ex $
        assume x (Ax: A x),
        have A x ∨ B x, from or.inl Ax,
        exists.intro x this,
    have h₂: (∃x, B x) → ∃x, A x ∨ B x, from
      assume h_ex,
      exists.elim h_ex $
        assume x (Bx: B x),
        have A x ∨ B x, from or.inr Bx,
        exists.intro x this,
    or.elim h h₁ h₂
end

section
  example (ex_A_and_B: ∃x, A x ∧ B x) (all_A_and_B_imp_C: ∀x, A x ∧ B x → C x)
  : ∃x, A x ∧ C x :=
    exists.elim ex_A_and_B $
      assume x (Ax_and_Bx: A x ∧ B x),
      have Ax_and_Bx_imp_Cx: A x ∧ B x → C x, from all_A_and_B_imp_C x,
      have Cx: C x, from Ax_and_Bx_imp_Cx Ax_and_Bx,
      have Ax: A x, from and.left Ax_and_Bx,
      have Ax_and_Cx: A x ∧ C x, from and.intro Ax Cx,
      exists.intro x Ax_and_Cx
end

section
  variable P: U → Prop
  variable T: U → U → Prop

  example (h: ∀x y, P x → ¬T y x): ∀x y, T y x → ¬P x :=
    assume x y,
    assume Tyx, 
    show ¬P x, from
      assume Px,
      have Px_imp_nTyx: P x → ¬T y x, from h x y,
      have nTyx: ¬T y x, from Px_imp_nTyx Px,
      show false, from nTyx Tyx
    
  example (h: ∀x y, T y x → ¬P x): ∀x y, P x → ¬T y x :=
    assume x y,
    assume Px, 
    show ¬T y x, from
      assume Tyx,
      have Tyx_imp_nPx: T y x → ¬P x, from h x y,
      have nPx: ¬P x, from Tyx_imp_nPx Tyx,
      show false, from nPx Px
end

section
  variables Y H: U → Prop

  variable h₁: ∀x, Y x ∧ H x → B x
  variable h₂: ∀x, A x → H x
  variable h₃: ∃x, Y x ∧ A x

  example: ∃x, B x :=
    exists.elim h₃ $
      assume x (Yx_and_Ax: Y x ∧ A x),
      have Yx: Y x, from and.left Yx_and_Ax,
      have Ax: A x, from and.right Yx_and_Ax,
      have Hx: H x, from h₂ x Ax,
      have Y x ∧ H x, from and.intro Yx Hx,
      have Bx: B x, from h₁ x this,
      exists.intro x Bx
end