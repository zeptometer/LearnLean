inductive iszero : nat → Prop
| iszero_0 : iszero 0
| iszero_S : ∀ n: nat, iszero (nat.succ n) → iszero n

example : ∀ n: nat, iszero n ↔ n = 0 :=
begin
    intros,
    split,
        intros,
        induction a,
            trivial,
        have : nat.succ a_n > 0,
            apply nat.zero_lt_succ,
        contradiction,
    intros,
    rw a,
    apply iszero.iszero_0,
end
