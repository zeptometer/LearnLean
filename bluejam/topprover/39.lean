example : (forall P Q R, (P <-> Q) \/ (Q <-> R) \/ (R <-> P)) -> forall P, P \/ ¬ P :=
begin
    intros,
    cases a (P ∨ ¬ P) ¬(P ∨ ¬ P) ¬¬(P ∨ ¬ P),
        simp * at *,
    simp * at *,
    apply h.mp,
    intro,
    have : ¬ P,
        from (
            assume h: P,
            have a : P ∨ ¬ P, from or.intro_left (¬ P) h,
            absurd a a_1
        ),
    have : P ∨ ¬ P, from (or.intro_right P this),
    contradiction,
end
