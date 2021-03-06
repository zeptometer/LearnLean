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

-- right-to-left requires classical logic?
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  iff.intro
    (
      assume h: ∀ x, p x,
      assume hn: ∃ x, ¬ p x,
      match hn with ⟨ w, hnw ⟩ :=
        absurd (h w) hnw
      end
    )
    (
      assume h: ¬ (∃ x, ¬ p x),
      assume y: α,
      show p y, from (
        by_contradiction (
          assume hy: ¬ p y,
          have ∃ x, ¬ p x, from exists.intro y hy,
          absurd this h
        )
      )
    )

-- right-to-left requires classical logic?
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  iff.intro
    (
      assume h: ∃ x, p x,
      assume hq: ∀ x, ¬ p x,
      match h with ⟨w, hw⟩ :=
        absurd hw (hq w)
      end
    )
    (
      assume h: ¬ (∀ x, ¬ p x),
      by_contradiction (
        assume hnp: ¬ (∃ x, p x),
        have ∀ x, ¬ p x, from (
          assume y: α,
          show ¬ p y, from (
            assume hy: p y,
            absurd (exists.intro y hy) hnp
          )
        ),
        absurd this h
      )
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (
      assume h: ¬ ∃ x, p x,
      assume y: α,
      assume hpy: p y,
      have ∃ x, p x, from exists.intro y hpy,
      absurd this h
    )
    (
      assume h: ∀ x, ¬ p x,
      assume he: ∃ x, p x,
      match he with ⟨w, hw⟩ :=
        absurd hw (h w)
      end
    )

-- left to right uses classical logic. But, it could be better...?
theorem not_forall_exists_not : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (
      assume h: ¬ ∀ x, p x,
      by_contradiction (
        assume hn: ¬ ∃ x, ¬ p x,
        have ∀ x, p x, from (
          assume y: α,
          show p y, from by_contradiction (
            assume hp: ¬ p y,
            have ∃ x, ¬ p x, from exists.intro y hp,
            absurd this hn
          )
        ),
        absurd this h
      )
    )
    (
      assume h: ∃ x, ¬ p x,
      assume hp: ∀ x, p x,
      match h with ⟨w, hw⟩ :=
        absurd (hp w) hw
      end
    )


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
  (
    assume h: ∀ x, p x → r,
    assume he: ∃ x, p x,
    match he with ⟨w, hw⟩ :=
      h w hw
    end
  )
  (
    assume h: (∃ x, p x) → r,
    assume y: α,
    assume hpy: p y,
    show r, from h (exists.intro y hpy)
  )

-- right-to-left requires classical logic?
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (
      assume h1: ∃ x, p x → r,
      assume h2: ∀ x, p x,
      match h1 with ⟨w, hw⟩ :=
        hw (h2 w)
      end
    )
    (
      assume h: (∀ x, p x) → r,
        by_cases
          (
            assume hp: ∀ x, p x,
            have r, from h hp,
            have p a → r, from (assume hp: p a, ‹ r › ),
            exists.intro a this
          )
          (
            assume hnp: ¬ ∀ x, p x,
            have ∃ x, ¬ p x, from (not_forall_exists_not α p).mp hnp,
            match this with ⟨w, hnw⟩ :=
              have p w → r, from (
                assume hw: p w,
                absurd hw hnw
              ),
              exists.intro w this
            end
          )
    )

-- right-to-left requires classical logic?
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (
      assume h: ∃ x, r → p x,
      assume hr: r,
      match h with ⟨w, hw⟩ :=
        exists.intro w (hw hr)
      end
    )
    (
      assume h: (r → ∃ x, p x),
      by_cases
        (
          assume hr: r,
          have ∃ x, p x, from h hr,
          match this with ⟨ w, hw ⟩ :=
            exists.intro w
              (
                assume hr2: r,
                show p w, from hw
              )
          end
        )
        (
          assume hnr: ¬ r,
          have r → p a, from (
            assume hr: r,
            absurd hr hnr
          ),
          exists.intro a this
        )
    )
