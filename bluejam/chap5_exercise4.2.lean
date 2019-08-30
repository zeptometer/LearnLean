
open classical
variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
begin
  intros,
  apply iff.intro,
    intro x,
    apply x,
    apply a,
  intros hr x,
  assumption
end
-- left to right requires classical logic
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
begin
  apply iff.intro,
    intros h,
    apply by_cases,
      intro hr,
      right,
      assumption,
    intro hnr,
    left,
    intro,
    have : p x ∨ r,
        apply h,
    cases this,
      assumption,
    contradiction,
  intros,
  cases a,
    left,
    apply a,
  right,
  assumption
end
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
  apply iff.intro,
    intros,
    apply a,
    assumption,
  intros,
  apply a,
  assumption
end
