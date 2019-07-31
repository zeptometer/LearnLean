open classical

variables p q r s : Prop

theorem t1 : p → q → p :=
begin
  intros hp hq,
  exact hp
end

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
begin
  intro hp,
  apply h₁,
  apply h₂,
  exact hp
end

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
    intro h,
    apply and.intro,
      exact h.right,
    exact h.left,
  intro h,
  apply and.intro,
    exact h.right,
  exact h.left
end
example : p ∨ q ↔ q ∨ p :=
begin
  apply iff.intro,
    intro h,
    apply or.elim h,
      intro hp,
      exact or.intro_right q hp,
    intro hq,
    exact or.intro_left p hq,
  intro h,
  apply or.elim h,
    intro hq,
    exact or.intro_right p hq,
  intro hp,
  exact or.intro_left q hp
end
