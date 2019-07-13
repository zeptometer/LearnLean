open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
    assume h: ∃ x: α, r,
    exists.elim h
        (
            assume w: α,
            assume hw: r,
            hw
        )
example : r → (∃ x : α, r) :=
    assume h: r,
    exists.intro a  h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
    iff.intro
        (
            assume h: ∃ x, p x ∧ r,
            exists.elim h
                (
                    assume w: α,
                    assume hw: p w ∧ r,
                    and.intro (exists.intro w hw.left) hw.right
                )
        )
        (
            assume h: (∃ x, p x) ∧ r,
            exists.elim h.left
                (
                    assume w: α,
                    assume hw: p w,
                    ⟨ w, (and.intro hw h.right)⟩ 
                )
        )


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
        (
            assume h: ∃ x, p x ∨ q x,
            exists.elim h
                (
                    assume w: α,
                    assume hw: p w ∨ q w,
                    or.elim hw
                        (
                            assume hwl: p w,
                            have ∃ x, p x, from exists.intro w hwl,
                            or.intro_left (∃ x, q x) this
                        )
                        (
                            assume hwr: q w,
                            have ∃ x, q x, from exists.intro w hwr,
                            or.intro_right (∃ x, p x) this
                        )
                )
        )
        (
            assume h: (∃ x, p x) ∨ (∃ x, q x),
            or.elim h
                (
                    assume hl: ∃ x, p x,
                    exists.elim hl
                        (
                            assume w: α,
                            assume he: p w,
                            ⟨ w, or.intro_left (q w) he ⟩ 
                        )
                )
                (
                    assume hr: ∃ x, q x,
                    exists.elim hr
                        (
                            assume w: α,
                            assume he: q w,
                            ⟨ w, or.intro_right (p w) he ⟩ 
                        )
                )
        )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∀ x, p x) →  ¬ (∃ x, ¬ p x) :=
    assume h: ∀ x, p x,
    assume hn: ∃ x, ¬ p x,
    match hn with ⟨ w, hnw ⟩ :=
        absurd (h w) hnw
    end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
