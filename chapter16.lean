import data.set data.int.basic data.set
open function int set

section
  def f (x : ℤ) : ℤ := x + 3
  def g (x : ℤ) : ℤ := -x
  def h (x : ℤ) : ℤ := 2 * x + 3

  example : injective h :=
    assume x₁ x₂,
    assume :2 * x₁ + 3 = 2 * x₂ + 3,
    have 2 * x₁ = 2 * x₂, from add_right_cancel this,
    show x₁ = x₂, from mul_left_cancel' (dec_trivial) this

  example : surjective g :=
    assume y,
    have g (-y) = y, from calc
      g (-y) = -(-y): rfl
      ... = y: neg_neg y,
    exists.intro (-y) this
    

  example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
    (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
  funext
    (assume x,
      calc
        v1 x = v1 (u (v2 x)) : by rw h2
        ... = v2 x          : by rw h1)
end

section
  variables {X Y : Type}
  variable  f : X → Y
  variables A B : set X

  example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  assume y,
  assume h1 : y ∈ f '' (A ∩ B),
  show y ∈ f '' A ∩ f '' B, from 
    exists.elim h1 $
      assume x h,
      have feq: f x = y, from and.right h,
      have x ∈ A ∩ B, from and.left h,
      have x ∈ A, from and.left ‹x ∈ A ∩ B›,
      have y ∈ f '' A, from exists.intro x $ ⟨this, feq⟩,
      have x ∈ B, from and.right ‹x ∈ A ∩ B›,
      have y ∈ f '' B, from exists.intro x $ ⟨this, feq⟩,
      ⟨‹y ∈ f '' A›, ‹y ∈ f '' B›⟩ 
end