inductive two
| c21
| c22

inductive three
| c31
| c32
| c33

lemma two_has_two_elements (a b c: two): a = b ∨ b = c ∨ c = a :=
begin
    cases a; cases b; cases c; repeat {refl <|> {left, refl} <|> right },
end

example : two ≠ three :=
begin
    intro,
    have h := two_has_two_elements,
    rw a at h,
    have := h three.c31 three.c32 three.c33,
    simp at this,
    assumption,
end
