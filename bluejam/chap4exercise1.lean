variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
        (
            assume h: ∀ x, (p x ∧ q x),
            have ∀ x, p x, from (
                assume x: α,
                show p x, from (h x).left
            ),
            have ∀ x, q x, from (
                assume x: α ,
                show q x, from (h x).right
            ),
            and.intro ‹ ∀ x, p x › ‹ ∀ x, q x › 
        )
        (
            assume h: (∀ x, p x) ∧ (∀ x, q x),
            assume y: α,
            have p y, from h.left y,
            have q y, from h.right y,
            show p y ∧ q y, from and.intro ‹ p y › ‹ q y › 
        )
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
