variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
begin
  apply iff.intro,
    intro h,
    split,
      intro x,
      apply (h x).left,
    intro x,
    exact (h x).right,
  intro h,
  intro x,
  split,
    apply h.left,
  apply h.right
end
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
begin
  intros,
  apply a,
  apply a_1
end
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  intros,
  cases a,
    left,
    apply a,
  right,
  apply a
end
