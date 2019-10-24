    
open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

-- This is required to add a to tactics
include a

example : (∃ x : α, r) → r :=
begin
  intros h,
  cases h,
  assumption
end
example : r → (∃ x : α, r) :=
begin
  intros,
  apply exists.intro,
  repeat { assumption }
end
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
begin
  apply iff.intro,
    intros,
    cases a_1 with x hpx,
    simp *,
    existsi x,
    simp *,
  intros,
  cases a_1.left with x hx,
  existsi x,
  simp *
end
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin
  apply iff.intro,
    intros,
    cases a_1 with w hw,
    cases hw with h,
      left,
      existsi w,
      assumption,
    right,
    existsi w,
    assumption,
  intros,
  cases a_1 with hp hq,
    cases hp with w hw,
    existsi w,
    simp *,
  cases hq with w hw,
  existsi w,
  simp *
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
  apply iff.intro,
    intros h hn,
    cases hn with w hw,
    simp * at *,
  intros,
  apply by_contradiction,
  intros,
  have : ∃ x, ¬ p x,
    apply exists.intro,
    apply a_2,
  contradiction
end
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
begin
  apply iff.intro,
    intros h hn,
    simp * at *,
    cases h,
    contradiction,
  intros h,
  apply by_contradiction,
  intros hn,
  have : ∀ x, ¬ p x,
    intros y,
    apply not.intro,
    intros hy,
    have : ∃ x, p x,
      apply exists.intro,
      assumption,
    contradiction,
  contradiction
end
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
  apply iff.intro,
    intros h x hp,
    have : ∃ x, p x,
      apply exists.intro,
      assumption,
    contradiction,
  intros h hp,
  cases hp with x hx,
  simp * at *
end
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
begin
  apply iff.intro,
    intros h,
    apply by_contradiction,
    intros hn,
    have : ∀ x, p x,
      intros y,
      apply by_contradiction,
      intro hny,
      have : ∃ x, ¬ p x,
        apply exists.intro,
        assumption,
      contradiction,
    contradiction,
  intros h hn,
  cases h with w hw,
  simp * at *
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
begin
  apply iff.intro,
    intros h1 h2,
    cases h2 with w hw,
    apply h1,
    exact hw,
  intros h x hx,
  apply h,
  existsi x,
  assumption
end
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
begin
  apply iff.intro,
    intros h1 h2,
    cases h1 with w hw,
    apply hw,
    simp [h2],
  intros h,
  apply by_cases,
    intros h1,
    have : r,
      apply h,
      assumption,
    existsi a,
    simp [h1 a, this],
  intros h1,
  have : ∃ x, ¬ p x,
    apply by_contradiction,
    intros h2,
    have : ∀ x, p x,
      intros,
        intros,
        apply by_contradiction,
        intro h3,
        have : ∃ x, ¬ p x,
          apply exists.intro,
          assumption,
        contradiction,  
      intros,
      apply by_contradiction,
      intro h3,
      contradiction,
  cases this with w hw,
  existsi w,
  simp * at *,
end
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
begin
  apply iff.intro,
    intros h hr,
    simp [hr] at h,
    assumption,
  intros h,
  apply by_cases,
    intros hr,
    have hp : ∃ x, p x,
      apply h,
      assumption,
    cases hp with w hw,
    apply exists.intro,
    intros,
    exact hw,
  intros hnr,
  simp * at *,
  existsi a,
  assumption
end
