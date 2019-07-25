section sec_4_6_1
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x),
    from assume h: (∀ x, p x ∧ q x),
    have (∀ x, p x), from assume x, (h x).left,
    have (∀ x, q x), from assume x, (h x).right, 
    by from and.intro (by assumption) this,
  have (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x),
    from assume h: (∀ x, p x) ∧ (∀ x, q x),
    assume x,
    ⟨h.left x, h.right x⟩,
  iff.intro (by assumption) (by assumption).
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

end sec_4_6_1
