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