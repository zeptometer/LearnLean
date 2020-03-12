inductive gcd : ℕ → ℕ → ℕ → Prop
| gcd_0 : ∀ n, gcd n 0 n
| gcd_step : ∀ n m p, gcd m n p → gcd (n + m) n p
| gcd_swap : ∀ n m p, gcd m n p → gcd n m p

example : forall n, gcd n (n + 1) 1 := begin
    intros n,
    apply gcd.gcd_swap,
    apply gcd.gcd_step,
    induction n,
    apply gcd.gcd_0,
    apply gcd.gcd_swap,
    rw nat.succ_eq_add_one,
    rw nat.add_comm n_n 1,
    apply gcd.gcd_step,
    apply gcd.gcd_swap,
    assumption
end