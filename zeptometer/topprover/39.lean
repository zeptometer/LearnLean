lemma pohe : ∀P, ¬(P ↔ ¬P) := begin
    intro P,
    intro w,
    have np : ¬ P, {
        intro hp,
        exact w.1 hp hp
    },
    exact np (w.2 np)
end

theorem boolean_hole :
    (∀ P Q R, (P ↔ Q) ∨ (Q ↔ R) ∨ (R ↔ P)) → ∀ P, P ∨ ¬ P := begin
    intros asm P,
    cases asm (P ∨ ¬P) ¬(P ∨ ¬P) ¬¬(P ∨ ¬P), {
        exfalso,
        apply pohe,
        assumption,
    }, cases h, {
        exfalso,
        apply pohe,
        assumption
    }, {
        apply h.1,
        intro n_pnp,
        have np : ¬ P, {
            intro p,
            apply n_pnp,
            left,
            assumption
        },
        apply n_pnp,
        right,
        assumption
    }
end
  