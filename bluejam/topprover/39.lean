example : (forall P Q R, (P <-> Q) \/ (Q <-> R) \/ (R <-> P)) -> forall P, P \/ ¬ P :=
begin
    intros,
    cases a true false P,
        have: false,
            apply true_ne_false,
            rw h,
        contradiction,
    cases h,
        right,
        intro,
        apply h.mpr,
        assumption,
    left,
    apply h.mpr,
    trivial,
end
