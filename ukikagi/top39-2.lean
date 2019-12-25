example: (∀ P Q R, (P ↔ Q) ∨ (Q ↔ R) ∨ (R ↔ P)) → ∀ P, P ∨ ¬P
:=
begin
    intros h P,
    cases h true false P with h1 h23,
        exfalso,
        apply h1.1,
        trivial,
    cases h23 with h2 h3,
        right,
        exact h2.2,
    -- case h3
        left,
        apply h3.2,
        trivial,
end
