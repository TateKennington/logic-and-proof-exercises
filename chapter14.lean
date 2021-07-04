section
  parameters {A : Type} {R : A → A → Prop}
  parameter (irreflR : irreflexive R)
  parameter (transR : transitive R)

  local infix < := R

  def R' (a b : A) : Prop := R a b ∨ a = b
  local infix ≤ := R'

  theorem reflR' (a : A) : a ≤ a :=
    have a = a, from refl a,
    show a ≤ a, from or.inr this

  theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c):
    a ≤ c :=
  have h₁: a < b → a ≤ c, from
    assume :a < b,
    have h₁: b < c → a ≤ c, from
      assume :b < c,
      have a < c, from transR ‹a < b› this,
      or.inl this,
    have h₂: b = c → a ≤ c, from
      assume :b = c, 
      or.inl $ eq.subst this ‹a < b›,
    or.elim h2 h₁ h₂,
  have h₂: a = b → a ≤ c, from
    assume :a = b,
    show a ≤ c, from eq.subst (eq.symm this) h2,
  or.elim h1 h₁ h₂

  theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b :=
  have h₁: a < b → a = b, from
    assume :a < b,
    have h₁: b < a → a = b, from
      assume :b < a,
      have a < a, from transR ‹a < b› ‹b < a›,
      have false, from irreflR a this,
      false.elim this,
    have h₂: b = a → a = b, from
      assume :b = a,
      eq.symm this,
    or.elim h2 h₁ h₂,
  have h₂: a = b → a = b, from
    assume :a = b,
    this,
  or.elim h1 h₁ h₂
end

section
  parameters {A : Type} {R : A → A → Prop}
  parameter (reflR : reflexive R)
  parameter (transR : transitive R)

  def S (a b : A) : Prop := R a b ∧ R b a

  example : transitive S :=
    assume a b c,
    assume h₁ :S a b,
    assume h₂ :S b c,
    have R a b, from and.left h₁,
    have R b a, from and.right h₁,
    have R b c, from and.left h₂,
    have R c b, from and.right h₂,
    have R a c, from transR ‹R a b› ‹R b c›, 
    have R c a, from transR ‹R c b› ‹R b a›,
    and.intro ‹R a c› ‹R c a›
end

section
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)

  theorem R_is_not_strict_partial_order :
    ¬(irreflexive R ∧ transitive R) :=
  assume h: irreflexive R ∧ transitive R,
  show false, from
    have transitive R, from and.right h,
    have R a c, from ‹transitive R› Rab Rbc,
    nRac this
end

section
  open nat

  example : 1 ≤ 4 :=
    show 1 ≤ 4, from le_add_right 1 3
end