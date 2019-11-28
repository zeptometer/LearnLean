inductive Two : Type
| C21 : Two
| C22 : Two

inductive Three : Type
| C31 : Three
| C32 : Three
| C33 : Three

theorem two_is_not_three : Two ≠ Three := begin
    intro two_is_three,
    have hatonosu : ∀a b c: Two, a = b ∨ b = c ∨ c = a :=
        by intros a b c; cases a; cases b; cases c; simp,
    rw two_is_three at hatonosu,
    have uso := hatonosu Three.C31 Three.C32 Three.C33,
    simp at uso,
    assumption
end
