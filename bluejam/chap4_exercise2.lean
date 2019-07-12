variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
    assume y: α,
    iff.intro
        (
            assume h: (∀ x: α, r),
            show r, from h y
        )
        (
            assume h: r,
            assume x: α,
            h
        )

-- example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
-- left to right requires classical logic
example : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) :=
    assume h: (∀ x, p x) ∨ r,
    or.elim h
        (
            assume h₁: ∀ x, p x,
            assume y: α,
            or.intro_left r (h₁ y)
        )
        (
            assume h₂: r,
            assume y: α,
            or.intro_right (p y) h₂
        )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
        (
            assume h: ∀ x, r → p x,
            assume hr: r,
            assume y: α,
            show p y, from (h y) hr
        )
        (
            assume h: r → ∀ x, p x,
            assume y: α,
            assume hr: r,
            show p y, from (h hr) y
        )
