import data.set
open set

section
  variable U: Type
  variables A B C: set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
    assume x,
    assume :x ∈ A ∩ C,
    have x ∈ A, from and.left this,
    show x ∈ A ∪ B, from or.inl this

  example : ∀ x, x ∈ (A ∪ B)ᶜ  → x ∈ Aᶜ :=
    assume x,
    assume :x ∈ (A ∪ B)ᶜ,
    have x ∈ Aᶜ ∩ Bᶜ, from eq.subst (compl_union A B) this,
    show x ∈ Aᶜ, from and.left this

end

section
  variable {U : Type}

  def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

  example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
      (h3 : D ⊆ B) :
    disj C D :=
  assume x,
  assume :x ∈ C,
  have x ∈ A, from h2 this,
  assume :x ∈ D,
  have x ∈ B, from h3 this,
  show false, from h1 ‹x ∈ A› ‹x ∈ B› 
  
end

section
  variables {I U : Type}
  variables (A : I → set U) (B : I → set U) (C : set U)

  example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
    assume x,
    assume h: x ∈ (⋂ i, A i) ∩ (⋂ i, B i),
    have x ∈ (⋂ i, A i), from and.left h,
    have x ∈ (⋂ i, B i), from and.right h,
    have ∀i, x ∈ A i, by simp * at *,
    have ∀i, x ∈ B i, by simp * at *,
    have ∀i, x ∈ A i ∩ B i, from
      assume i: I,
      have x ∈ A i, from ‹∀i, x ∈ A i› i,
      have x ∈ B i, from ‹∀i, x ∈ B i› i,
      show x ∈ A i ∩ B i, from and.intro ‹x ∈ A i› ‹x ∈ B i›,
    show x ∈ (⋂ i, A i ∩ B i), by simp * at *

  example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
    assume x,
    assume h: x ∈ C ∩ (⋃i, A i),
    have x ∈ C, from and.left h,
    have x ∈ (⋃i, A i), from and.right h,
    have ∃i, x ∈ A i, from by simp * at *,
    have ∃i, x ∈ C ∩ A i, from exists.elim this $
      assume i,
      assume :x ∈ A i,
      have x ∈ C ∩ A i, from and.intro ‹x ∈ C› this,
      exists.intro i this,
    show x ∈ ⋃i, C ∩ A i, by simp * at *
    
end

section
  variable  {U : Type}
  variables A B C : set U

  example (h : A ⊆ B) : powerset A ⊆ powerset B :=
    assume x,
    assume :x ∈ powerset A,
    show x ∈ powerset B, from subset.trans this h

  example (h : powerset A ⊆ powerset B) : A ⊆ B :=
    show A ⊆ B, from h (subset.refl A)
end