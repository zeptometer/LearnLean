inductive iszero : ℕ → Prop
| iszero_0 : iszero 0
| iszero_S : ∀ n, iszero (nat.succ n) → iszero n

example (n) : iszero n ↔ n = 0 := begin
    constructor,
    intro n_is_zero,
    induction n_is_zero, {
        refl
    }, {
       cases n_is_zero_ih,
    }, {
        intro n_is_zero,
        rw n_is_zero,
        apply iszero.iszero_0
    }
end