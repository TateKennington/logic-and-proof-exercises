import data.int.basic

section
  variable A : Type
  variable f : A → A
  variable P : A → Prop
  variable h : ∀ x, P x → P (f x)

  -- Show the following:
  example : ∀ y, P y → P (f (f y)) :=
    assume y,
    assume Py: P y,
    have Py_imp_Pfy: P y → P (f y), from h y,
    have Pfy: P (f y), from Py_imp_Pfy Py,
    have Pfy_imp_Pffy: P (f y) → P (f(f y)), from h (f y),
    show P (f (f y)), from Pfy_imp_Pffy Pfy
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=
    assume h,
    assume x,
    have Ax_and_Bx: A x ∧ B x, from h x,
    show A x, from and.left Ax_and_Bx
end

section
  variable U : Type
  variables A B C : U → Prop

  variable h1 : ∀ x, A x ∨ B x
  variable h2 : ∀ x, A x → C x
  variable h3 : ∀ x, B x → C x

  example : ∀ x, C x :=
    assume x,
    have Ax_or_Bx: A x ∨ B x, from h1 x,
    have Ax_imp_Cx: A x → C x, from h2 x,
    have Bx_imp_Cx: B x → C x, from h3 x,
    show C x, from or.elim Ax_or_Bx Ax_imp_Cx Bx_imp_Cx
end

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x

  example : false :=
    have h_barber: shaves barber barber ↔ ¬ shaves barber barber, from h barber,
    have h1: ¬shaves barber barber,
      from assume h_shaves,
      show false, from (h_barber.elim_left h_shaves) h_shaves,
    show false, from h1 (h_barber.elim_right h1)
end

section
  variable U : Type
  variables A B : U → Prop

  example : (∃ x, A x) → ∃ x, A x ∨ B x :=
    assume h,
    exists.elim h $
      assume x (h1: A x),
      have A x ∨ B x, from or.inl h1,
      exists.intro x this
end

section
  variable U : Type
  variables A B : U → Prop

  variable h1 : ∀ x, A x → B x
  variable h2 : ∃ x, A x

  example : ∃ x, B x :=
   exists.elim h2 $
    assume x (Ax : A x),
    have Ax_imp_Bx: A x → B x, from h1 x,
    have B x, from Ax_imp_Bx Ax,
    exists.intro x this
end

section
  variable  U : Type
  variables A B C : U → Prop

  example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
  ∃ x, A x ∧ C x :=
    exists.elim h1 $
      assume x (Ax_and_Bx: A x ∧ B x),
      have Bx_imp_Cx: B x → C x, from h2 x,
      have Ax: A x, from and.left Ax_and_Bx,
      have Bx: B x, from and.right Ax_and_Bx,
      have Cx: C x, from Bx_imp_Cx Bx,
      have Ax_and_Cx: A x ∧ C x, from and.intro Ax Cx,
      exists.intro x Ax_and_Cx
end

section
  variable  U : Type
  variables A B C : U → Prop

  example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
    assume h,
    assume x,
    assume Ax,
    have exists_Ax: ∃x, A x, from exists.intro x Ax,
    show false, from h exists_Ax

  example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
    assume h,
    assume exists_Ax,
    exists.elim exists_Ax $
      assume x (Ax: A x),
      have ¬A x, from h x,
      show false, from this Ax
end

section
  variable  U : Type
  variables R : U → U → Prop

  example : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
    assume h,
    exists.elim h $
      assume x (h₁: ∀ y, R x y),
      assume y,
      have Rxy: R x y, from h₁ y,
      exists.intro x Rxy
end

section
  variable {A : Type}
  variables {a b c : A}

  theorem foo {A : Type} {a b c : A} : a = b → c = b → a = c :=
  sorry

  theorem my_symm (h : b = a) : a = b :=
    have a = a, from rfl,
    show a = b, from foo ‹a = a› h

  theorem my_trans (h1 : a = b) (h2 : b = c) : a = c :=
    have c = b, from my_symm h2,
    show a = c, from foo h1 ‹c = b›
end

section
  variables x y z : ℤ

  theorem t1 : x - x = 0 :=
  calc
  x - x = x + -x : by rw sub_eq_add_neg
      ... = 0      : by rw add_right_neg

  theorem t2 (h : x + y = x + z) : y = z :=
  calc
  y     = 0 + y        : by rw zero_add
      ... = (-x + x) + y : by rw add_left_neg
      ... = -x + (x + y) : by rw add_assoc
      ... = -x + (x + z) : by rw h
      ... = (-x + x) + z : by rw add_assoc
      ... = 0 + z        : by rw add_left_neg
      ... = z            : by rw zero_add

  theorem t3 (h : x + y = z + y) : x = z :=
  calc
  x     = x + 0        : by rw add_zero
      ... = x + (y + -y) : by rw add_right_neg
      ... = (x + y) + -y : by rw add_assoc
      ... = (z + y) + -y : by rw h
      ... = z + (y + -y) : by rw add_assoc
      ... = z + 0        : by rw add_right_neg
      ... = z            : by rw add_zero

  theorem t4 (h : x + y = 0) : x = -y :=
  calc
  x     = x + 0        : by rw add_zero
      ... = x + (y + -y) : by rw add_right_neg
      ... = (x + y) + -y : by rw add_assoc
      ... = 0 + -y       : by rw h
      ... = -y           : by rw zero_add

  theorem t5 : x * 0 = 0 :=
  have h1 : x * 0 + x * 0 = x * 0 + 0, from
  calc
      x * 0 + x * 0 = x * (0 + 0) : by rw left_distrib
              ... = x * 0       : by rw add_zero
              ... = x * 0 + 0   : by rw add_zero,
  show x * 0 = 0, from t2 _ _ _ h1

  theorem t6 : x * (-y) = -(x * y) :=
  have h1 : x * (-y) + x * y = 0, from
  calc
      x * (-y) + x * y = x * (-y + y) : by rw left_distrib
                  ... = x * 0        : by rw add_left_neg
                  ... = 0            : by rw t5 x,
  show x * (-y) = -(x * y), from t4 _ _ h1

  theorem t7 : x + x = 2 * x :=
  calc
  x + x = 1 * x + 1 * x : by rw one_mul
      ... = (1 + 1) * x   : by rw right_distrib
      ... = 2 * x         : rfl
end