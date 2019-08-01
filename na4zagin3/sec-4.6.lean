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
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume Hpq: ∀ x, p x → q x,
  assume Hp: ∀ x, p x,
  assume x,
  show q x, from ((Hpq x) (Hp x)).
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  have (∀ x, p x) → ∀ x, p x ∨ q x,
    from assume Hp x, or.intro_left _ (Hp x),
  have (∀ x, q x) → ∀ x, p x ∨ q x,
    from assume Hq x, or.intro_right _ (Hq x),
  assume h, or.elim h (by assumption) (by assumption).

end sec_4_6_1

section sec_4_6_2
variables (α : Type) (p q : α → Prop)
variable r : Prop

/- Without Classic -/
example : α → ((∀ x : α, r) ↔ r) :=
  assume a: α,
  have (∀ x : α, r) → r,
    from assume Hr, Hr a,
  have r → (∀ x : α, r),
    from assume r x, r,
  iff.intro ‹(∀ x : α, r) → r› ‹r → (∀ x : α, r)›.
theorem thm2 : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) :=
  have (∀ x, p x) → (∀ x, p x ∨ r),
    from assume Hp x, or.intro_left _ (Hp x),
  have r → (∀ x, p x ∨ r),
    from assume Hr x, or.intro_right _ Hr,
  assume Hpr,
  or.elim Hpr (by assumption) (by assumption).
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  have (∀ x, r → p x) → (r → ∀ x, p x),
    from assume Hrp r x, Hrp x r,
  have (r → ∀ x, p x) → (∀ x, r → p x),
    from assume Hrp x r, Hrp r x,
  iff.intro (by assumption) (by assumption).

/- With Classic -/
open classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  have (∀ x, p x ∨ r) → (∀ x, p x) ∨ r,
    from assume Hpr,
      have r → (∀ x, p x) ∨ r,
        from assume Hr, or.intro_right _ Hr,
      have ¬ r → (∀ x, p x),
        from assume Hnr x,
          have p x ∨ r, from Hpr x,
        sorry,
    sorry,
  sorry.

end sec_4_6_2
