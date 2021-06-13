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

section

  example: ∀(x:U) y z, x = z → z = y → x = y :=
   assume x y z (h₁: x = z) (h₂: z = y),
   calc
    x = z: h₁
    ... = y: by rw h₂
end

section
  variables x y : U
  variable h₁: ∀(x: U), x = x
  variable h₂: ∀(u:U) v w, u = w → v = w → u = v

  example: x = y → y = x :=
    assume h,
    have y = y, from h₁ y,
    show y = x, from (h₂ y x y) ‹y = y› h
end

section
  example: (¬∃x,A x ∧ B x) ↔ (∀x,A x → ¬B x) :=
    have h₁: (¬∃x,A x ∧ B x) → (∀x,A x → ¬B x), from
      assume h,
      assume x,
      assume Ax,
      show ¬B x, from
        assume Bx,
        have Ax_and_Bx: A x ∧ B x, from and.intro Ax Bx,
        have ∃x, A x ∧ B x, from exists.intro x Ax_and_Bx,
        show false, from h this,
    have h₂: (∀x,A x → ¬B x) → (¬∃x,A x ∧ B x) , from
      assume h,
      show ¬∃x,A x ∧ B x, from
        assume h_ex,
        show false, from exists.elim h_ex $
          assume x (Ax_and_Bx: A x ∧ B x),
          have Ax: A x, from and.left Ax_and_Bx,
          have Bx: B x, from and.right Ax_and_Bx,
          have Ax_imp_nBx: A x → ¬B x, from h x,
          have nBx: ¬B x, from Ax_imp_nBx Ax,
          show false, from nBx Bx,
    iff.intro h₁ h₂
end

section
  open classical

  example: (¬∀x, A x → B x) ↔ (∃x, A x ∧ ¬B x) :=
    have h₁: (¬∀x, A x → B x) → (∃x, A x ∧ ¬B x), from
      assume h,
      show ∃x, A x ∧ ¬B x, from by_contradiction $
        assume h_nex: ¬∃x, A x ∧ ¬B x,
        show false, from
          have ∀x, A x → B x, from
            assume x,
            assume Ax,
            show B x, from by_contradiction $
              assume nBx,
              have A x ∧ ¬B x, from and.intro Ax nBx,
              have h_ex: ∃x, A x ∧ ¬B x, from exists.intro x this,
              show false, from h_nex h_ex,
          show false, from h this,
    have h₂: (∃x, A x ∧ ¬B x) → (¬∀x, A x → B x) :=
      assume h,
      assume h_all,
      show false, from
        exists.elim h $
          assume x (Ax_and_nBx: A x ∧ ¬B x),
          have Ax_imp_Bx: A x → B x, from h_all x,
          have A x, from and.left Ax_and_nBx,
          have Bx: B x, from Ax_imp_Bx this,
          have nBx: ¬B x, from and.right Ax_and_nBx,
          show false, from nBx Bx,
    iff.intro h₁ h₂
end

section
  example(h:∃x, A x ∧ ∀y, A y → y = x): ∃x, A x ∧ ∀y,∀z, A y ∧ A z → y = z :=
    exists.elim h $
      assume x (h₁: A x ∧ ∀y, A y → y = x),
      have Ax: A x, from and.left h₁,
      have all_A_imp_eq_x: ∀y, A y → y = x, from and.right h₁,
      have ∀y,∀z, A y ∧ A z → y = z, from
        assume (y:U) (z:U) (Ay_and_Az: A y ∧ A z),
        have Ay_imp_y_eq_x: A y → y = x, from all_A_imp_eq_x y,
        have Az_imp_z_eq_x: A z → z = x, from all_A_imp_eq_x z,
        have A y, from and.left Ay_and_Az,
        have y_eq_x: y = x, from Ay_imp_y_eq_x this,
        have A z, from and.right Ay_and_Az,
        have z_eq_x: z = x, from Az_imp_z_eq_x this,
        show y = z, by rw [y_eq_x, z_eq_x],
      exists.intro x (and.intro Ax this)
    
  example(h:∃x, A x ∧ ∀y,∀z, A y ∧ A z → y = z): ∃x, A x ∧ ∀y, A y → y = x :=
    exists.elim h $
      assume x (h₁: A x ∧ ∀y,∀z, A y ∧ A z → y = z),
      have Ax: A x, from and.left h₁,
      have h₂: ∀y,∀z, A y ∧ A z → y = z, from and.right h₁,
      have ∀y, A y → y = x, from
        assume y Ay,
        have A y ∧ A x → y = x, from h₂ y x,
        show y = x, from this (and.intro Ay Ax),
      exists.intro x (and.intro Ax this)
end