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
  have : ∃ x, ¬ p x, from exists.intro x a_2,
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
  have : ∀ x, ¬ p x, from (
    assume y : α,
    begin
      apply not.intro,
      intros hy,
      have : ∃ x, p x, from exists.intro y hy,
      contradiction
    end
  ),
  contradiction
end
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
  apply iff.intro,
    intros h x hp,
    have : ∃ x, p x, from exists.intro x hp,
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
    have : ∀ x, p x, from (
      assume y : α,
      begin
        apply by_contradiction,
        intro hny,
        have : ∃ x, ¬ p x, from (exists.intro y hny),
        contradiction
      end
    ),
    contradiction,
  intros h hn,
  cases h with w hw,
  simp * at *
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
