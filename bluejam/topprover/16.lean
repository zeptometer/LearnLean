inductive gcd: nat → nat → nat → Prop
| zero : ∀ (n : nat), gcd n 0 n
| step : ∀ (n m p : nat), gcd m n p → gcd (n + m) n p
| swap : ∀ (n m p : nat), gcd m n p → gcd n m p

example : ∀ n : nat, gcd n (n + 1) 1 :=
begin
    intros,
    apply gcd.swap,
    apply gcd.step,
    induction n,
        apply gcd.zero,
    apply gcd.swap,
    rw [←nat.add_one, add_comm],
    apply gcd.step,
    apply gcd.swap,
    assumption,
end
